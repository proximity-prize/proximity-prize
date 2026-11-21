import ProximityPrize.SubmissionLower.Low48PrimaryPivotSectionSum

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators
open private band_card from ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
open private binWeight from ProximityPrize.SubmissionLower.Low48PrimaryPivotSectionSum

private def qMin (w : Window) : ℤ := 4650-(w.diagonalHi : ℤ)

private def gradeOK (w : Window) (q l : ℤ) : Prop :=
  (w.gradeLo : ℤ)-3000 ≤ l-q ∧ l-q < (w.gradeHi : ℤ)-3000

private instance (w : Window) (q l : ℤ) : Decidable (gradeOK w q l) := by
  unfold gradeOK
  infer_instance

private theorem weight_card (w : Window) (p : Triple) (q : ℤ) :
    (((Ico (indexLo w) (indexHi w p)).filter (gradeOK w q)).card : ℤ) =
      binWeight w p.index q := by
  let hi := min ((p.index : ℤ)+1) (1651-(w.offsetLo : ℤ))
  let lo := indexLo w
  have eq : ((Ico lo (indexHi w p)).filter (gradeOK w q)) =
      Ico (max lo (q+(w.gradeLo : ℤ)-3000)) (min hi (q+(w.gradeHi : ℤ)-3000)) := by
    ext l
    simp only [mem_filter,mem_Ico,gradeOK,max_le_iff,lt_min_iff]
    have hhi : indexHi w p = max lo hi := by
      simp [indexHi,lo,hi,min_comm]
    rw [hhi]
    omega
  rw [show indexLo w = lo by rfl,eq,Int.card_Ico]
  simp only [binWeight,indexLo,lo,hi]
  omega

private def weightGrid (w : Window) (p : Triple) : Finset (ℤ × ℤ) :=
  ((Ico (qMin w) (orderHi w)).product (Ico (indexLo w) (indexHi w p))).filter
    (fun x => (p.contact : ℤ) < x.1 ∧ gradeOK w x.1 x.2)

private def columnGrid (w : Window) (p : Triple) : Finset (ℤ × ℤ) :=
  ((Ico (indexLo w) (indexHi w p)).product (Ico (orderLo w p) (orderHi w))).filter
    (fun x => gradeOK w x.2 x.1)

private theorem swap_grids (w : Window) (p : Triple) :
    (columnGrid w p).card = (weightGrid w p).card := by
  refine Finset.card_bij (fun x _ => (x.2,x.1)) ?_ ?_ ?_
  · rintro ⟨l,q⟩ h
    obtain ⟨hp, hg⟩ := Finset.mem_filter.mp h
    obtain ⟨hl, hq⟩ := Finset.mem_product.mp hp
    have ho := Finset.mem_Ico.mp hq
    simp only [orderLo] at ho
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ?_, hl⟩, ?_, hg⟩
    · unfold qMin; omega
    · omega
  · rintro ⟨l,q⟩ _ ⟨l',q'⟩ _ h
    cases h
    rfl
  · rintro ⟨q,l⟩ h
    refine ⟨(l,q),?_,rfl⟩
    obtain ⟨hp, hc, hg⟩ := Finset.mem_filter.mp h
    obtain ⟨hq,hl⟩ := Finset.mem_product.mp hp
    have ho := Finset.mem_Ico.mp hq
    unfold qMin at ho
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hl,Finset.mem_Ico.mpr ?_⟩,hg⟩
    unfold orderLo
    omega

theorem columnFee2_eq_bins (w : Window) (p : Triple) (hg : w.gradeLo ≤ w.gradeHi)
    (hp : p.index ≤ 1650) :
    columnFee2 w p = 2*(∑ q ∈ Ico (qMin w) (orderHi w),
      if (p.contact : ℤ) < q then binWeight w p.index q else 0) := by
  have hband := band_card (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
    ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
    (le_max_left _ _) (min_le_left _ _) (by omega)
  change 2*((columnGrid w p).card : ℤ) = _ at hband
  rw [columnFee2,ite_eq_left hp,← hband,swap_grids]
  unfold weightGrid
  rw [natCast_card_filter]
  have hprod := sum_product (Ico (qMin w) (orderHi w)) (Ico (indexLo w) (indexHi w p))
    (fun x : ℤ × ℤ => if (p.contact : ℤ) < x.1 ∧ gradeOK w x.1 x.2 then (1 : ℤ) else 0)
  refine (congrArg (fun z : ℤ => 2*z) hprod).trans ?_
  congr 1
  apply sum_congr rfl
  intro q _
  by_cases hc : (p.contact : ℤ) < q
  · simp only [hc,true_and,ite_true]
    rw [← natCast_card_filter,weight_card]
  · simp [hc]

#print axioms columnFee2_eq_bins
end Low48PrimaryPivot

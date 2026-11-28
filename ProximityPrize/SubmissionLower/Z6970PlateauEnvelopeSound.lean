import ProximityPrize.SubmissionLower.Z6970PlateauEnvelopeFacts

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace ExpandedPlateauEnvelope6970
open KoalaPiecewiseTriangle (Line)
open KoalaLinearWindow (Span)
open ExpandedPlateauIntegral6970 (delta value receipt_eq)
open ExpandedPlateauSum6970 (lines sumN spanLength)
open Finset
open scoped BigOperators

theorem integrate_sum (lo hi : ℤ) (l : Line) (ls : List Line)
    (pos : ∀ k ∈ l::ls, 0 < k.d) (ord : (l::ls).Pairwise (fun a b => a.d < b.d)) :
    integrate lo hi l ls = ∑ x ∈ (⟨lo,hi⟩ : Span).finset, delta (top x l ls) := by
  induction ls generalizing lo hi l with
  | nil => exact bill_sum lo hi l (pos l (by simp))
  | cons k ks ih =>
    by_cases empty : hi ≤ lo
    · simp [integrate,empty,Span.finset,Ico_eq_empty_of_le empty]
    let t := switchAt hi l (k::ks)
    obtain ⟨higher,sorted⟩ := List.pairwise_cons.mp ord
    have boundary (x : ℤ) := switch_iff hi x l (k::ks) higher
    have left (x : ℤ) (hx : x ∈ (⟨lo,t⟩ : Span).finset) :
        top x l (k::ks) = l.at x := by
      apply max_eq_left
      apply top_le
      intro a ha
      by_contra! h
      have passed : t ≤ x := (boundary x).mpr (Or.inr ⟨a,ha,h.le⟩)
      have before : x < t := (mem_Ico.mp hx).2
      exact (not_lt_of_ge passed) before
    have right (x : ℤ) (hx : x ∈ (⟨max lo t,hi⟩ : Span).finset) :
        top x l (k::ks) = top x k ks := by
      apply max_eq_right
      obtain ⟨lb,ub⟩ := mem_Ico.mp hx
      obtain h | ⟨a,ha,ht⟩ := (boundary x).mp ((le_max_right lo t).trans lb)
      · exact False.elim ((not_lt_of_ge h) (show x < hi from ub))
      · exact ht.trans (le_top x k a ks ha)
    simp only [integrate,if_neg empty]
    change billFast lo t l + integrate (max lo t) hi k ks = _
    rw [bill_sum lo t l (pos l (by simp)),
      ih (max lo t) hi k (fun a ha => pos a (List.mem_cons_of_mem _ ha)) sorted,
      cut_sum lo hi t (fun x => delta (top x l (k::ks))) (switch_le hi l (k::ks))]
    congr 1
    · exact sum_congr rfl (fun x hx => congrArg delta (left x hx).symm)
    · exact sum_congr rfl (fun x hx => congrArg delta (right x hx).symm)

theorem equivalent_strip (f c r : ℕ) : strip f c r = ExpandedPlateauSum6970.strip f c r := by
  by_cases h : spanLength c f r = 0
  · simp [strip,ExpandedPlateauSum6970.strip,h]
  · simp only [strip,ExpandedPlateauSum6970.strip,h,ite_false]
    let ls := lines (c:ℤ) (f:ℤ) (r:ℤ)
    have pos : ∀ k ∈ ls.1::ls.2, 0 < k.d := by
      simp [ls,lines]
    have ord : (ls.1::ls.2).Pairwise (fun a b => a.d < b.d) := by
      simp [ls,lines]
    change integrate 0 _ ls.1 ls.2 = ExpandedPlateauIntegral6970.receipt _ ls.1 ls.2
    rw [integrate_sum _ _ _ _ pos ord, receipt_eq]
    apply sum_congr rfl
    intro x _
    congr 1
    cases ht : ls.2 with
    | nil => rfl
    | cons k ks => exact (value_top (ls.1.at x) x k ks).symm

theorem equivalent_columns (f start len : ℕ) :
    ExpandedPlateauSum6970.columnChunk f start len = columns f start len := by
  unfold ExpandedPlateauSum6970.columnChunk columns
  congr 1
  funext i
  simp only [column,ExpandedPlateauSum6970.column,equivalent_strip]

end ExpandedPlateauEnvelope6970

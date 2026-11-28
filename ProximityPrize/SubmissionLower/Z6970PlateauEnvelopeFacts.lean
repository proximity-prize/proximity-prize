import ProximityPrize.SubmissionLower.Z6970PlateauEnvelope

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ExpandedPlateauEnvelope6970
open KoalaPiecewiseTriangle (Line)
open KoalaLinearWindow (Span)
open ExpandedPlateauIntegral6970 (poly clipped bill delta value)
open Finset
open scoped BigOperators

theorem crosses (l k : Line) (x : ℤ) (h : l.d < k.d) :
    cross l k ≤ x ↔ l.at x ≤ k.at x := by
  unfold cross
  rw [neg_le, Int.le_ediv_iff_mul_le (show 0 < k.d-l.d by omega), neg_mul,
    mul_sub, mul_comm x k.d, mul_comm x l.d]
  unfold Line.at
  omega

theorem switch_le (hi : ℤ) (l : Line) (ls : List Line) : switchAt hi l ls ≤ hi := by
  induction ls with
  | nil => exact le_rfl
  | cons k ks ih => exact (min_le_right _ _).trans ih

theorem switch_iff (hi x : ℤ) (l : Line) (ls : List Line)
    (hd : ∀ k ∈ ls, l.d < k.d) :
    switchAt hi l ls ≤ x ↔ hi ≤ x ∨ ∃ k ∈ ls, l.at x ≤ k.at x := by
  induction ls with
  | nil => simp [switchAt]
  | cons k ks ih =>
    have h := ih (fun t ht => hd t (List.mem_cons_of_mem _ ht))
    rw [switchAt, min_le_iff, crosses _ _ _ (hd k (by simp)), h]
    constructor
    · rintro (hk | hb | ⟨a,ha,ht⟩)
      · exact Or.inr ⟨k,by simp,hk⟩
      · exact Or.inl hb
      · exact Or.inr ⟨a,List.mem_cons_of_mem _ ha,ht⟩
    · rintro (hb | ⟨a,ha,ht⟩)
      · exact Or.inr (Or.inl hb)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact Or.inl ht
        · exact Or.inr (Or.inr ⟨a,ha,ht⟩)

def top (x : ℤ) (l : Line) : List Line → ℤ
  | [] => l.at x
  | k :: ks => max (l.at x) (top x k ks)

theorem value_top (v x : ℤ) (l : Line) (ls : List Line) :
    value v x (l :: ls) = max v (top x l ls) := by
  induction ls generalizing v l with
  | nil => rfl
  | cons k ks ih =>
    change value (max v (l.at x)) x (k :: ks) = max v (max (l.at x) (top x k ks))
    rw [ih, max_assoc]

theorem top_le (x v : ℤ) (l : Line) (ls : List Line)
    (h : ∀ a ∈ l :: ls, a.at x ≤ v) : top x l ls ≤ v := by
  induction ls generalizing l with
  | nil => exact h l (by simp)
  | cons k ks ih =>
    exact max_le (h l (by simp)) (ih k (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem le_top (x : ℤ) (l a : Line) (ls : List Line) (ha : a ∈ l :: ls) :
    a.at x ≤ top x l ls := by
  induction ls generalizing l with
  | nil => simp only [List.mem_singleton] at ha; subst a; exact le_rfl
  | cons k ks ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact le_max_left _ _
    · exact (ih k h).trans (le_max_right _ _)

theorem clipped_fast_eq (lo hi : ℤ) (l : Line) (hd : 0 < l.d) :
    clippedFast lo hi l = clipped (⟨lo,hi⟩ : Span) l := by
  simp only [clippedFast,clipped,Span.keep,if_pos hd,Span.size,Line.at]
  split
  · rename_i h
    have hz : (hi - max lo (-(l.a/l.d))).toNat = 0 := Int.toNat_of_nonpos (by omega)
    simp [hz,poly]
  · rfl

theorem bill_sum (lo hi : ℤ) (l : Line) (hd : 0 < l.d) :
    billFast lo hi l = ∑ x ∈ (⟨lo,hi⟩ : Span).finset, delta (l.at x) := by
  unfold billFast
  split
  · rename_i h
    simp [Span.finset,Ico_eq_empty_of_le h]
  · rw [clipped_fast_eq lo hi l hd, clipped_fast_eq lo hi (⟨l.a-1835,l.d⟩ : Line) hd]
    exact ExpandedPlateauIntegral6970.bill_eq _ _

theorem cut_sum (lo hi t : ℤ) (g : ℤ → ℤ) (h : t ≤ hi) :
    (∑ x ∈ (⟨lo,hi⟩ : Span).finset, g x) =
      (∑ x ∈ (⟨lo,t⟩ : Span).finset, g x) +
      ∑ x ∈ (⟨max lo t,hi⟩ : Span).finset, g x := by
  have hu : Ico lo t ∪ Ico (max lo t) hi = Ico lo hi := by
    ext x
    simp only [mem_union,mem_Ico,max_le_iff]
    omega
  have hd : Disjoint (Ico lo t) (Ico (max lo t) hi) := by
    apply disjoint_left.mpr
    intro x hx hy
    simp only [mem_Ico,max_le_iff] at hx hy
    omega
  unfold Span.finset
  rw [← hu, sum_union hd]

end ExpandedPlateauEnvelope6970

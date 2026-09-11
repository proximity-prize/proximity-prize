import ProximityPrize.SubmissionLower.Part.G094


section Compact_SecondJetRowIntervals
/-! Interval checking for arbitrary finite piecewise-affine rows, including
activation jumps of a second-jet profile. -/
namespace ProximityPrize.SubmissionLower.SecondJetRowIntervals
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxHeartbeats 3000000

def pickTail (z : ℕ) (a : BaseSegment) : List BaseSegment → BaseSegment
  | [] => a
  | s::ss => pickTail z (if s.start ≤ z then s else a) ss

def baseSlopeAt (q : BaseRow) (lo : ℕ) : ℕ :=
  match q.segments with
  | [] => 0
  | a::ss => (pickTail lo a ss).slope

def BaseCell (q : BaseRow) (lo hi : ℕ) : Prop :=
  lo=hi ∨ (3 ≤ lo ∧ match q.segments with
    | [] => True
    | a::ss => a.start ≤ lo ∧ ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start)
instance (q : BaseRow) (lo hi : ℕ) : Decidable (BaseCell q lo hi) := by
  unfold BaseCell
  cases q.segments <;> infer_instance

theorem fold_pick (z : ℕ) (a : BaseSegment) (ss : List BaseSegment) :
    ss.foldl (fun best next => if next.start ≤ z then next else best) a = pickTail z a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldl_cons,pickTail]
    exact ih _

theorem pick_stable (lo hi z : ℕ) (a : BaseSegment) (ss : List BaseSegment)
    (h : ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start) (hz : lo ≤ z) (hhi : z ≤ hi) :
    pickTail z a ss = pickTail lo a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    have hs := h s (by simp)
    have hss : ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start := fun s hs => h s (by simp [hs])
    rcases hs with hs | hs
    · simp only [pickTail,if_pos hs,if_pos (hs.trans hz)]
      exact ih _ hss
    · simp only [pickTail,if_neg (show ¬s.start ≤ z by omega),if_neg (show ¬s.start ≤ lo by omega)]
      exact ih _ hss

theorem pick_start (lo : ℕ) (a : BaseSegment) (ss : List BaseSegment) (ha : a.start ≤ lo) :
    (pickTail lo a ss).start ≤ lo := by
  induction ss generalizing a with
  | nil => exact ha
  | cons s ss ih =>
    simp only [pickTail]
    split
    · exact ih _ (by assumption)
    · exact ih _ ha

theorem segment_evalAt_shift (s : BaseSegment) (lo z : ℕ)
    (hs : s.start ≤ lo) (hz : lo ≤ z) :
    s.evalAt z = s.evalAt lo+s.slope*(z-lo) := by
  have hsplit : z-s.start = (lo-s.start)+(z-lo) := by omega
  simp only [BaseSegment.evalAt,hsplit,Nat.mul_add]
  omega

theorem baseAt_affine (q : BaseRow) (lo hi z : ℕ)
    (hcell : BaseCell q lo hi) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    q.evalAt z = q.evalAt lo+baseSlopeAt q lo*(z-lo) := by
  rcases hcell with heq | ⟨hlo3,hcell⟩
  · have hz : z=lo := by omega
    subst z
    simp
  · have hz3 : 3 ≤ z := hlo3.trans hlo
    simp only [BaseRow.evalAt,if_neg (show z≠0 by omega),if_neg (show z≠1 by omega),
      if_neg (show z≠2 by omega),if_neg (show lo≠0 by omega),if_neg (show lo≠1 by omega),
      if_neg (show lo≠2 by omega)]
    cases hs : q.segments with
    | nil => simp [hs,evalBaseSegments,baseSlopeAt]
    | cons a ss =>
      rw [hs] at hcell
      simp only at hcell
      simp only [hs,evalBaseSegments,baseSlopeAt,fold_pick]
      rw [pick_stable lo hi z a ss hcell.2 hlo hhi]
      exact segment_evalAt_shift _ lo z (pick_start lo a ss hcell.1) hlo

end ProximityPrize.SubmissionLower.SecondJetRowIntervals

end Compact_SecondJetRowIntervals

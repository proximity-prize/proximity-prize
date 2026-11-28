import ProximityPrize.SubmissionLower.Z6970H2307OrderEval

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Height2307WidePrefix
open K1_13_2 (cumulative denominator cappedCount)
open Low6969GateCell (cappedN capped_eq denN denN_eq dg den_eq)

def tailCount (d j : ℕ) : ℤ :=
  (denN j : ℤ) - dg j (d+1) - dg j (d+2) - dg j (d+3) - dg j 1503

private theorem cumulative_simple {d j : ℤ} (hd : 0≤d) (hj : 0≤j) (h : j<2*d+3) (h' : j≤3*d) :
    cumulative d j = denominator j - denominator (j-d-1) -
      denominator (j-d-2) - denominator (j-d-3) := by
  have h3 : j-2*d-3<0 := by omega
  have h4 : j-2*d-4<0 := by omega
  have h5 : j-2*d-5<0 := by omega
  have h6 : j-3*d-6<0 := by omega
  have hz (u : ℤ) (hu : u<0) : denominator u=0 := by simp [denominator,hu]
  simp only [cumulative,show ¬d<0 by omega,show ¬j<0 by omega,
    Bool.false_or,decide_false,Bool.false_eq_true,if_false,min_eq_left h',
    hz _ h3,hz _ h4,hz _ h5,hz _ h6,add_zero,sub_zero]

theorem tailCount_eq (d j : ℕ) (hd : 1060≤d) (hj : j≤1679) : tailCount d j = cappedN d j 500 := by
  rw [← capped_eq]
  have hr : cumulative ((d : ℤ)-501) ((j : ℤ)-1503) = denominator ((j : ℤ)-1503) := by
    by_cases h : (j : ℤ)-1503<0
    · simp [cumulative,denominator,h]
    · rw [cumulative_simple (by omega) (by omega) (by omega) (by omega)]
      have hz (u : ℤ) (hu : u<0) : denominator u=0 := by simp [denominator,hu]
      rw [hz ((j : ℤ)-1503-((d : ℤ)-501)-1) (by omega),
        hz ((j : ℤ)-1503-((d : ℤ)-501)-2) (by omega),
        hz ((j : ℤ)-1503-((d : ℤ)-501)-3) (by omega)]
      ring
  unfold cappedCount
  rw [if_neg (show ¬ ((500 : ℕ) : ℤ) < 0 from by decide),
    show (d : ℤ)-((500 : ℕ) : ℤ)-1=(d : ℤ)-501 by norm_num <;> ring,
    show (j : ℤ)-3*(((500 : ℕ) : ℤ)+1)=(j : ℤ)-1503 by norm_num]
  rw [hr,cumulative_simple (by omega) (by omega) (by omega) (by omega)]
  unfold tailCount
  rw [← denN_eq,← den_eq j (d+1),← den_eq j (d+2),← den_eq j (d+3),
    ← den_eq j 1503]
  push_cast
  ring_nf

def solidTail (w j : ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | fuel+1, start, span =>
    if span=0 then 0 else let take := min w span
    (take : ℤ) * tailCount (ExpandedTaper6970.cap start) j +
      solidTail w j fuel (start+take) (span-take)

theorem solidTail_eq (w j fuel start span : ℕ) (hj : j≤1679)
    (hs : 3514≤start) (he : start+span≤4025) :
    solidTail w j fuel start span = upperTail w j fuel start span := by
  induction fuel generalizing start span with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : span=0
      · simp [solidTail,upperTail,h]
      · simp only [solidTail,upperTail,if_neg h]
        have hd : 1060≤ExpandedTaper6970.cap start := by
          unfold ExpandedTaper6970.cap
          rw [if_neg (by omega)]
          omega
        rw [tailCount_eq _ _ hd hj]
        exact congrArg _ (ih _ _ (by omega) (by have := min_le_right w span; omega))

theorem flatTail (w j fuel start span : ℕ) (hw : 0<w)
    (hf : span≤fuel) (hj : j≤ExpandedTaper6970.cap (start+span-1)) :
    upperTail w j fuel start span = (span : ℤ)*cappedN j j 500 := by
  induction fuel generalizing start span with
  | zero =>
      have h : span=0 := by omega
      simp [upperTail,h]
  | succ fuel ih =>
      by_cases h : span=0
      · simp [upperTail,h]
      · let take := min w span
        have ht : take ≤ span := min_le_right _ _
        have ht' : 0<take := by unfold take; omega
        have hc : j≤ExpandedTaper6970.cap start := hj.trans
          (ExpandedTaper6970.cap_antitone (show start≤start+span-1 by omega))
        have hcap : cappedN (ExpandedTaper6970.cap start) j 500 = cappedN j j 500 := by
          rw [← capped_eq,← capped_eq]
          exact (capped_stable (le_refl _) hc).symm
        have he : j≤ExpandedTaper6970.cap (start+take+(span-take)-1) := by
          rwa [show start+take+(span-take)-1=start+span-1 by omega]
        simp only [upperTail,if_neg h,← show min w span = take by rfl]
        change (take : ℤ) * cappedN (ExpandedTaper6970.cap start) j 500 +
          upperTail w j fuel (start+take) (span-take) = _
        rw [hcap,ih (start+take) (span-take) (by omega) he,Int.ofNat_sub ht]
        ring

def countMemo (b j w : ℕ) : ℤ :=
  let span := b-3513
  fastPrefix (min b 3513) j +
    (if 0<w ∧ j≤ExpandedTaper6970.cap (3514+span-1) then (span : ℤ)*cappedN j j 500
     else solidTail w j 512 3514 span)

theorem countMemo_eq (b j w : ℕ) (hb : b≤4024) (hj : j≤1679) :
    countMemo b j w = countUpper b j w := by
  unfold countMemo countUpper
  dsimp only
  split
  · rename_i h
    rw [flatTail w j 512 3514 (b-3513) h.1 (by omega) h.2]
  · rw [solidTail_eq w j 512 3514 (b-3513) hj le_rfl (by omega)]

end Height2307WidePrefix

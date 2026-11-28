import ProximityPrize.SubmissionLower.Z6970ExpandedMoments

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace ExpandedColumns6970
open Finset
open K1_13_2 (cappedCount cumulative)
open TaperMoments (cumPrefix cumulative_prefix)
open scoped BigOperators

def signedPrefix (d : ℤ) (n : ℕ) : ℤ := if d < 0 then 0 else cumPrefix d.toNat n

private theorem signedPrefix_eq (d : ℤ) (n : ℕ) :
    signedPrefix d n = 24 * ∑ u ∈ range n, cumulative d (u : ℤ) := by
  by_cases hd : d < 0
  · simp [signedPrefix, cumulative, hd]
  · have hc : (d.toNat : ℤ) = d := by omega
    simpa only [signedPrefix, if_neg hd, hc] using (cumulative_prefix d.toNat n).symm

private theorem shift_prefix (d : ℤ) :
    (∑ u ∈ range 1679, cumulative d ((u : ℤ)-1503)) =
      ∑ u ∈ range 176, cumulative d (u : ℤ) := by
  calc
    _ = ∑ u ∈ range (1503+176), cumulative d ((u : ℤ)-1503) := rfl
    _ = _ := by
      rw [sum_range_add]
      have hzero : (∑ u ∈ range 1503, cumulative d ((u : ℤ)-1503)) = 0 := by
        apply sum_eq_zero
        intro u hu
        have hu' := mem_range.mp hu
        have h : (u : ℤ)-1503 < 0 := by omega
        simp [cumulative,h]
      rw [hzero, zero_add]
      apply sum_congr rfl
      intro u _
      have hu : (((1503+u : ℕ) : ℤ)-1503) = u := by push_cast; ring
      exact congrArg (cumulative d) hu

theorem indexMomentFast (d : ℕ) :
    indexMoment d = 24*1679*cappedCount (d : ℤ) 1679 500 -
      signedPrefix d 1679 + signedPrefix ((d : ℤ)-501) 176 := by
  unfold indexMoment
  have hsum : (∑ u ∈ range 1679, cappedCount (d : ℤ) (u : ℤ) 500) =
      (∑ u ∈ range 1679, cumulative (d : ℤ) (u : ℤ)) -
      ∑ u ∈ range 176, cumulative ((d : ℤ)-501) (u : ℤ) := by
    simp only [cappedCount, show ¬ (500 : ℤ) < 0 by decide, if_false]
    rw [sum_sub_distrib]
    have hx : (d : ℤ)-500-1 = (d : ℤ)-501 := by ring
    simp only [hx, show (3 : ℤ)*(500+1)=1503 by decide]
    exact congrArg (fun z : ℤ => (∑ u ∈ range 1679, cumulative (d : ℤ) (u : ℤ))-z)
      (shift_prefix ((d : ℤ)-501))
  rw [hsum, signedPrefix_eq, signedPrefix_eq]
  ring

abbrev TripleMoment := ℤ × ℤ × ℤ

def addMoment (a b : TripleMoment) : TripleMoment :=
  (a.1+b.1,a.2.1+b.2.1,a.2.2+b.2.2)

def computeRow (q : ℕ) : TripleMoment :=
  let d := gradeCap q
  let c := cappedCount (d : ℤ) 1679 500
  (c, q*c, 24*1679*c - signedPrefix d 1679 + signedPrefix ((d : ℤ)-501) 176)

def compute (lo : ℕ) : ℕ → TripleMoment
  | 0 => (0,0,0)
  | n+1 => addMoment (compute lo n) (computeRow (lo+n))

theorem compute_eq (lo n : ℕ) :
    compute lo n =
      (∑ i ∈ range n, cappedCount (gradeCap (lo+i)) 1679 500,
       ∑ i ∈ range n, ((lo+i : ℕ) : ℤ)*cappedCount (gradeCap (lo+i)) 1679 500,
       ∑ i ∈ range n, indexMoment (gradeCap (lo+i))) := by
  induction n with
  | zero => simp [compute]
  | succ n ih => simp only [compute, ih, addMoment, computeRow, sum_range_succ, indexMomentFast]

theorem compute_add (lo a b : ℕ) : compute lo (a+b) =
    addMoment (compute lo a) (compute (lo+a) b) := by
  induction b with
  | zero => simp [compute, addMoment]
  | succ b ih =>
      rw [show a+(b+1) = a+b+1 by omega, compute, compute, ih,
        Nat.add_assoc lo a b]
      rcases compute lo a with ⟨a0,a1,a2⟩
      rcases compute (lo+a) b with ⟨b0,b1,b2⟩
      rcases computeRow (lo+a+b) with ⟨c0,c1,c2⟩
      simp [addMoment,Int.add_assoc,Nat.add_assoc]

end ExpandedColumns6970

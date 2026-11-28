import ProximityPrize.SubmissionLower.Z6970ExpandedPivotOptRows

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ExpandedPivotOpt6970

def Triple.floorChoice (p : Triple) : ℕ :=
  min p.fourthCap
    (min ((p.b+p.c-p.room)/2) ((p.b + (500-p.f)-p.room)/3))

theorem fourth_eq_floor (p : Triple) : p.fourth = p.floorChoice := by
  unfold Triple.fourth Triple.floorChoice
  dsimp
  split
  · rename_i h
    obtain ⟨hCap,hGain⟩ := h
    simp only [Triple.gainAt] at hGain
    omega
  · rfl

theorem contact_eq_gain (p : Triple) :
    p.contact = p.c+2*p.f+p.room+p.gainAt p.floorChoice := by
  have h : p.floorChoice ≤ p.fourthCap := min_le_left _ _
  rw [Triple.fourthCap] at h
  simp only [Triple.contact, Triple.packet, Groups.gain, fourth_eq_floor, Triple.gainAt]
  omega

end ExpandedPivotOpt6970

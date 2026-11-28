import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.AlternateDispatch

theorem raiseWeight {i : Fin 18} {r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region}
    {al w lo : ℕ} {ah hi : Option ℕ}
    (lower : lo ≤ max w (r.graph*(131071-2313)-1))
    (all : _root_.Research6970.Height2313.Research6969.PairRoute.Done i ⟨r,al,ah,lo,hi⟩) :
    _root_.Research6970.Height2313.Research6969.PairRoute.Done i ⟨r,al,ah,w,hi⟩ := by
  intro s h
  have graph := h.root.2.2.2.1
  have native : r.graph*(131071-2313)-1 ≤ _root_.Research6970.Height2313.Research6969.NormalGeometry.weight s :=
    graph ▸ _root_.Research6970.Height2313.Research6969.NormalGeometry.base s
  exact all s ⟨h.root,h.al,h.ah,lower.trans (max_le h.wl native),h.wh⟩


theorem start {i : Fin 18} {r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region}
    (all : _root_.Research6970.Height2313.Research6969.PairRoute.Done i ⟨r,0,none,r.graph*(131071-2313)-1,none⟩) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done i r := by
  intro s h
  have graph := h.2.2.2.1
  exact all s ⟨h,Nat.zero_le _,by simp,graph ▸ _root_.Research6970.Height2313.Research6969.NormalGeometry.base s,by simp⟩

end Research6970.Height2313.Research6969.AlternateDispatch


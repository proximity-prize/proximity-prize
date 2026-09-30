import ProximityPrize.SubmissionLower.BalancedPhasePotential6815
namespace ProximityPrize.SubmissionLower.TerminalPotentials6815
open BalancedPhasePotential6815 PhasePotential6815 RCN260 AsymmetricHelper
theorem count0 (r y t : ℕ) (hr : 1≤r) (hR : r≤39) (hY : y≤182) (hT : t≤11192) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤0*t+4690861953401*y+43345274666350*r := by
  simpa only [Nat.zero_mul,Nat.zero_add] using final_pass_count r y t hr hY hT
theorem count1 (r y t : ℕ) (hr : 1≤r) (hR : r≤28) (hY : y≤131) (hT : t≤8092) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤53657045892*t+3381036458565*y+15633886130566*r := by
  exact count_le 88902 1382 308 28 131 8092 53657045892 3381036458565 15633886130566 r y t (by decide +kernel) hr hR hY hT
theorem count2 (r y t : ℕ) (hr : 1≤r) (hR : r≤26) (hY : y≤124) (hT : t≤7692) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤50287772707*t+3174905420834*y+14829154405166*r := by
  exact count_le 88902 1382 308 26 124 7692 50287772707 3174905420834 14829154405166 r y t (by decide +kernel) hr hR hY hT
theorem count3 (r y t : ℕ) (hr : 1≤r) (hR : r≤25) (hY : y≤117) (hT : t≤7692) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤47864909186*t+3114024297937*y+14402986544890*r := by
  exact count_le 88902 1382 308 25 117 7692 47864909186 3114024297937 14402986544890 r y t (by decide +kernel) hr hR hY hT
theorem count4 (r y t : ℕ) (hr : 1≤r) (hR : r≤24) (hY : y≤114) (hT : t≤7692) :
    leftRegularCountCap (pair 88902 1382 308 r y t)≤46285733583*t+3053143175041*y+14220343176200*r := by
  exact count_le 88902 1382 308 24 114 7692 46285733583 3053143175041 14220343176200 r y t (by decide +kernel) hr hR hY hT
end ProximityPrize.SubmissionLower.TerminalPotentials6815

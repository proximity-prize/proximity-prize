/- Apache-2.0. Transfer the packed partition bound to the actual terminal degree. -/
import ProximityPrize.SubmissionLower.CheckedGrid
import ProximityPrize.SubmissionLower.Night6836CapData
namespace Koala6836.Bound
set_option maxRecDepth 30000
set_option maxHeartbeats 1500000
private theorem caps (r e:ℕ) (hr:1≤r) (ru:r≤18) (hy:r+e≤76) : Fast.capOK r e=true := by
  have ck : Fast.capRow r=true := by
    interval_cases r
    · exact Fast.cap1
    · exact Fast.cap2
    · exact Fast.cap3
    · exact Fast.cap4
    · exact Fast.cap5
    · exact Fast.cap6
    · exact Fast.cap7
    · exact Fast.cap8
    · exact Fast.cap9
    · exact Fast.cap10
    · exact Fast.cap11
    · exact Fast.cap12
    · exact Fast.cap13
    · exact Fast.cap14
    · exact Fast.cap15
    · exact Fast.cap16
    · exact Fast.cap17
    · exact Fast.cap18
  exact List.all_eq_true.mp ck _ (List.mem_range.mpr (by omega))
theorem room (r e t k:ℕ) (rp:1≤r) (rh:r≤18) (ym:r+e≤76) (yl:r+e≤t)
    (top:t≤min 9352 (Room.maxTotal r e)) (small:k≤(t-(r+e))/100) :
    many r e k ≤ Room.budget r e t := by
  obtain ⟨ht,hard⟩ := le_min_iff.mp top
  have hk:k<94 := by omega
  obtain ⟨d,check⟩ := Bool.and_eq_true_iff.mp (caps r e rp rh ym)
  have ordered : Room.lowBudget r e≤Room.highBudget r e := of_decide_eq_true d
  have minDeg:r+e+100*k≤t := by omega
  have bound := (of_decide_eq_true (List.all_eq_true.mp check k (List.mem_range.mpr hk))) (minDeg.trans hard)
  change many r e k ≤ Room.budget r e (r+e+100*k) at bound
  apply bound.trans
  unfold Room.budget
  split <;> split <;> first | exact le_rfl | exact ordered | omega
#print axioms room
end Koala6836.Bound

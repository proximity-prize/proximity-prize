import ProximityPrize.SubmissionLower.FinalCurves6815
import ProximityPrize.SubmissionLower.MovingFiberSingletonGeometry6815
namespace ProximityPrize.SubmissionLower.SingletonCurveChecks6815
open FinalCurves6815 MovingFiberSingleCore6815
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 50000

def carrier (r v : ℕ) : Carrier :=
  ⟨MovingFiberShape6815.cost r v 0,MovingFiberShape6815.cost r v 1,MovingFiberShape6815.cost r v 2,
    MovingFiberShape6815.cost r v 3,MovingFiberShape6815.cost r v 4⟩
theorem carrier_correct (r v : ℕ) : (carrier r v).Correct r v := ⟨rfl,rfl,rfl,rfl,rfl⟩

def pointCheck (r v w lo hi z : ℕ) (start : ℕ) (p : Piece) : Bool :=
  if lo≤z ∧ z≤hi then Nat.ble (choice (carrier r v) w r v z) (value p start z) else true

theorem pointCheck_sound (r v w lo hi z start : ℕ) (p : Piece)
    (h : pointCheck r v w lo hi z start p=true) (hl : lo≤z) (hh : z≤hi) :
    choice (carrier r v) w r v z≤value p start z := by
  simpa only [pointCheck,if_pos (show lo≤z ∧ z≤hi from ⟨hl,hh⟩),Nat.ble_eq] using h

def high (r v w lo hi : ℕ) (start : ℕ) (p : Piece) : Bool :=
  let a := max lo 3
  if a≤hi then Nat.ble (choice (carrier r v) w r v a) (value p start a) &&
    Nat.ble (choice (carrier r v) w r v hi) (value p start hi) else true

def checkPair (r v : ℕ) (th : Array ℕ) (start : ℕ) (p : Piece) (runStart : ℕ) (run : Piece) : Bool :=
  let lo := max start runStart
  let stop := min p.stop run.stop
  if lo<stop then
    decide (Active th run.base r v lo (stop-1)) &&
    pointCheck r v run.base lo (stop-1) 0 start p && pointCheck r v run.base lo (stop-1) 1 start p &&
    pointCheck r v run.base lo (stop-1) 2 start p && high r v run.base lo (stop-1) start p
  else true

theorem checkPair_sound (r v : ℕ) (th : Array ℕ) (start : ℕ) (p : Piece)
    (runStart : ℕ) (run : Piece) (z : ℕ)
    (hc : checkPair r v th start p runStart run=true)
    (hp : start≤z) (hp' : z<p.stop) (hr : runStart≤z) (hr' : z<run.stop) :
    Active th run.base r v z z ∧ choice (carrier r v) run.base r v z≤value p start z := by
  let lo := max start runStart
  let hi := min p.stop run.stop-1
  have hn : max start runStart<min p.stop run.stop := by omega
  simp only [checkPair,if_pos hn,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ha,h0⟩,h1⟩,h2⟩,hh⟩ := hc
  have hlo : lo≤z := by dsimp only [lo]; omega
  have hhi : z≤hi := by dsimp only [hi]; omega
  have hzActive : Active th run.base r v z z := by
    exact active_at th run.base r v lo hi z ha hlo hhi
  refine ⟨hzActive,?_⟩
  by_cases hz3 : 3≤z
  · have ha3 : max lo 3≤hi := by omega
    change high r v run.base lo hi start p=true at hh
    simp only [high,if_pos ha3,Bool.and_eq_true,Nat.ble_eq] at hh
    have hl3 : start≤max lo 3 := by dsimp only [lo]; omega
    have hbound := TriangularAffine6815.shifted_between (max lo 3) hi z (max lo 3) start
      (choice (carrier r v) run.base r v (max lo 3)) p.base
      (choiceSlope (carrier r v) run.base r v) p.slope le_rfl hl3 (by omega) hhi
      (by simpa only [value,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hh.1)
      (by rw [←choice_affine (carrier r v) run.base r v (max lo 3) hi (le_max_right _ _) ha3]; exact hh.2)
    rwa [←choice_affine (carrier r v) run.base r v (max lo 3) z (le_max_right _ _) (by omega)] at hbound
  · have hpoint : z=0 ∨ z=1 ∨ z=2 := by omega
    rcases hpoint with rfl | rfl | rfl
    · exact pointCheck_sound r v run.base lo hi 0 start p h0 hlo hhi
    · exact pointCheck_sound r v run.base lo hi 1 start p h1 hlo hhi
    · exact pointCheck_sound r v run.base lo hi 2 start p h2 hlo hhi

def check (r v : ℕ) (th : Array ℕ) (curve runs : List Piece) : Bool :=
  validFrom (11193-r-v) 0 curve && validFrom (11193-r-v) 0 runs &&
    allCells (fun lo p => allCells (checkPair r v th lo p) 0 runs) 0 curve

theorem check_sound (r v : ℕ) (th : Array ℕ) (curve runs : List Piece)
    (hc : check r v th curve runs=true) (z : ℕ) (hz : z<11193-r-v) :
    ∃ w, Active th w r v z z ∧ choice (carrier r v) w r v z≤FinalCurves6815.eval curve z := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨lo,p,hlo,hhi,he,hp⟩ := cell_at _ 0 _ curve hc.1.1 (allCells_sound _ 0 curve hc.2) z (Nat.zero_le _) hz
  obtain ⟨rlo,run,hrlo,hrhi,_,hcheck⟩ := cell_at _ 0 _ runs hc.1.2 (allCells_sound _ 0 runs hp) z (Nat.zero_le _) hz
  have h := checkPair_sound r v th lo p rlo run z hcheck hlo hhi hrlo hrhi
  exact ⟨run.base,h.1,by simpa only [FinalCurves6815.eval,he] using h.2⟩

end ProximityPrize.SubmissionLower.SingletonCurveChecks6815

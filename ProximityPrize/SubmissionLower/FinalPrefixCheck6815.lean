import ProximityPrize.SubmissionLower.PackingSemantics6815
import ProximityPrize.SubmissionLower.TerminalPotentials6815
import ProximityPrize.SubmissionLower.MovingFiberPhaseCore6815
namespace ProximityPrize.SubmissionLower.FinalPrefixCheck6815
open FinalCurves6815
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

def affine (p : Potential) (r v z : ℕ) : ℕ :=
  p.totalCoeff*(r+v+z)+p.middleCoeff*(r+v)+p.slopeCoeff*r

theorem affine_shift (p : Potential) (r v lo z : ℕ) (h : lo≤z) :
    affine p r v z=affine p r v lo+p.totalCoeff*(z-lo) := by
  unfold affine
  rw [show r+v+z=(r+v+lo)+(z-lo) by omega]
  ring

def clippedPiece (slope base lower upper start : ℕ) (p : Piece) : Bool :=
  let lo := max lower start
  let hi := min upper p.stop
  if lo<hi then Nat.ble (value p start lo) (base+slope*lo) &&
    Nat.ble (value p start (hi-1)) (base+slope*(hi-1)) else true

def clipped (slope base lower upper : ℕ) (curve : List Piece) : Bool :=
  allCells (clippedPiece slope base lower upper) 0 curve

theorem clipped_sound (slope base lower upper finish : ℕ) (curve : List Piece)
    (hv : validFrom finish 0 curve=true) (hc : clipped slope base lower upper curve=true)
    (z : ℕ) (hl : lower≤z) (hu : z<upper) (hz : z<finish) :
    eval curve z≤base+slope*z := by
  obtain ⟨lo,p,hlo,hhi,he,hp⟩ := cell_at _ 0 finish curve hv
    (allCells_sound _ 0 curve hc) z (Nat.zero_le _) hz
  have hn : max lower lo<min upper p.stop := by omega
  simp only [clippedPiece,if_pos hn,Bool.and_eq_true,Nat.ble_eq] at hp
  have hh := TriangularAffine6815.shifted_between (max lower lo) (min upper p.stop-1) z lo 0
    p.base base p.slope slope (le_max_right _ _) (Nat.zero_le _) (by omega) (by omega)
    (by simpa only [value,Nat.sub_zero] using hp.1)
    (by simpa only [value,Nat.sub_zero] using hp.2)
  simpa only [eval,he,value,Nat.sub_zero] using hh

def phase (j : ℕ) : Potential :=
  if j<7 then (Lower80899.TenPhase.sound j).potential else Lower80899.SourceSound.PhaseFinal.potential
def sourceIndex (j : ℕ) := if j<7 then j else 5
def terminal : ℕ → Potential
  | 0 => ⟨0,4690861953401,43345274666350⟩
  | 1 => ⟨53657045892,3381036458565,15633886130566⟩
  | 2 => ⟨50287772707,3174905420834,14829154405166⟩
  | 3 => ⟨47864909186,3114024297937,14402986544890⟩
  | _ => ⟨46285733583,3053143175041,14220343176200⟩

def floorR : ℕ → ℕ | 0 => 0 | 1 => 11 | 2 => 13 | 3 => 14 | _ => 15
def floorY : ℕ → ℕ | 0 => 0 | 1 => 51 | 2 => 58 | 3 => 65 | _ => 68
def floorT : ℕ → ℕ | 0 => 0 | 1 => 3100 | _ => 3500
def shapeEligible (k r v : ℕ) : Prop := floorR k≤r ∧ floorY k≤r+v
instance (k r v : ℕ) : Decidable (shapeEligible k r v) := by unfold shapeEligible; infer_instance
def eligible (k r v z : ℕ) : Prop := shapeEligible k r v ∧ floorT k≤r+v+z
instance (k r v z : ℕ) : Decidable (eligible k r v z) := by unfold eligible; infer_instance
def classify (r v z : ℕ) : ℕ :=
  if eligible 4 r v z then 4 else if eligible 3 r v z then 3 else
    if eligible 2 r v z then 2 else if eligible 1 r v z then 1 else 0
def lower (k r v : ℕ) := floorT k-(r+v)
def upper (k r v : ℕ) := if k<4 ∧ shapeEligible (k+1) r v then lower (k+1) r v else 11193

theorem class_lt_five (r v z : ℕ) : classify r v z<5 := by unfold classify; split_ifs <;> omega

theorem class_interval (r v z : ℕ) (hz : z<11193) :
    shapeEligible (classify r v z) r v ∧ lower (classify r v z) r v≤z ∧
      z<upper (classify r v z) r v := by
  unfold classify
  split_ifs <;>
    simp_all [eligible,shapeEligible,floorR,floorY,floorT,lower,upper] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

def phaseCheck (r v cut intercept j : ℕ) (curve : List Piece) : Bool :=
  clipped (phase j).totalCoeff (affine (phase j) r v 0+intercept) 0 cut curve

theorem phaseCheck_sound (r v cut intercept j finish z : ℕ) (curve : List Piece)
    (hv : validFrom finish 0 curve=true) (hc : phaseCheck r v cut intercept j curve=true)
    (hz : z<finish) (hcut : z<cut) :
    eval curve z≤affine (phase j) r v z+intercept := by
  have h := clipped_sound _ _ 0 cut finish curve hv hc z (Nat.zero_le _) hcut hz
  rw [affine_shift (phase j) r v 0 z (Nat.zero_le _)]
  simpa only [Nat.sub_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def classCheck (r v cut intercept k : ℕ) (present : Bool) (curve : List Piece) : Bool :=
  if shapeEligible k r v then
    clipped (terminal k).totalCoeff (affine (terminal k) r v 0+intercept)
      (lower k r v) (min cut (upper k r v)) curve &&
    (if lower k r v<min cut (min (upper k r v) (11193-r-v)) then present else true)
  else true

theorem classCheck_sound (r v cut intercept k z : ℕ) (present : Bool) (curve : List Piece)
    (hv : validFrom (11193-r-v) 0 curve=true)
    (hc : classCheck r v cut intercept k present curve=true)
    (hk : classify r v z=k) (hz : z<11193-r-v) (hcut : z<cut) :
    eval curve z≤affine (terminal k) r v z+intercept ∧ present=true := by
  have hi := class_interval r v z (by omega)
  rw [hk] at hi
  simp only [classCheck,if_pos hi.1,Bool.and_eq_true] at hc
  have h := clipped_sound _ _ _ _ _ curve hv hc.1 z hi.2.1 (lt_min hcut hi.2.2) hz
  have hn : lower k r v<min cut (min (upper k r v) (11193-r-v)) := by omega
  simp only [if_pos hn] at hc
  refine ⟨?_,hc.2⟩
  rw [affine_shift (terminal k) r v 0 z (Nat.zero_le _)]
  simpa only [Nat.sub_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem rectangle_mono {α : Type*} [Preorder α] (f : ℕ → ℕ → α) (Rcap Ycap : ℕ)
    (hR : ∀ r v, r+1≤Rcap → r+1+v≤Ycap → f r v≤f (r+1) v)
    (hV : ∀ r v, r≤Rcap → r+v+1≤Ycap → f r v≤f r (v+1))
    (r v R V : ℕ) (hr : r≤R) (hv : v≤V) (hcap : R≤Rcap) (hy : R+V≤Ycap) :
    f r v≤f R V := by
  have ha : f r v≤f R v := by
    induction R,hr using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih (by omega) (by omega) |>.trans (hR n v (by omega) (by omega))
  apply ha.trans
  induction V,hv using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih (by omega) |>.trans (hV R n hcap (by omega))

end ProximityPrize.SubmissionLower.FinalPrefixCheck6815

import ProximityPrize.SubmissionLower.FinalLedgerChord6815
import ProximityPrize.SubmissionLower.FinalCurves6815
namespace ProximityPrize.SubmissionLower.FinalLedgerChecks6815
open FinalCurves6815 FinalLedgerChord6815
set_option autoImplicit false
set_option maxHeartbeats 1800000

def budget : ℕ := 274980718452113030
def cut0 (y : ℕ) := (11192-y)-(229-y)
def cut1 (r y : ℕ) := (11192-y)-min (50-r) (229-y)

def part (r y start : ℕ) (p : Piece) (lo hi mode : ℕ) : Bool :=
  if lo≤hi then decide (Fits r y start p.base p.slope lo hi mode budget) else true

def checkPiece (r y start : ℕ) (p : Piece) : Bool :=
  part r y start p start (min (p.stop-1) (cut0 y)) 0 &&
  part r y start p (max start (cut0 y+1)) (min (p.stop-1) (cut1 r y)) 1 &&
  part r y start p (max start (cut1 r y+1)) (p.stop-1) 2

theorem part_sound (r y start : ℕ) (p : Piece) (lo hi mode z : ℕ)
    (h : part r y start p lo hi mode=true) (hz : lo≤z) (hh : z≤hi) :
    combined (value p start z) r y z≤budget := by
  have hr : lo≤hi := hz.trans hh
  simp only [part,if_pos hr,decide_eq_true_eq] at h
  exact fits_between r y start p.base p.slope lo hi mode budget z h hz hh

theorem piece_sound (r y start : ℕ) (p : Piece) (h : checkPiece r y start p=true)
    (z : ℕ) (hz : start≤z) (hh : z<p.stop) : combined (value p start z) r y z≤budget := by
  simp only [checkPiece,Bool.and_eq_true] at h
  by_cases h0 : z≤cut0 y
  · exact part_sound r y start p start (min (p.stop-1) (cut0 y)) 0 z h.1.1 hz (by omega)
  by_cases h1 : z≤cut1 r y
  · exact part_sound r y start p (max start (cut0 y+1)) (min (p.stop-1) (cut1 r y)) 1 z h.1.2 (by omega) (by omega)
  · exact part_sound r y start p (max start (cut1 r y+1)) (p.stop-1) 2 z h.2 (by omega) (by omega)

def checkRow (r v : ℕ) (curve : List Piece) : Bool :=
  validFrom (11193-r-v) 0 curve && allCells (checkPiece r (r+v)) 0 curve

theorem row_sound (r v : ℕ) (curve : List Piece) (h : checkRow r v curve=true)
    (z : ℕ) (hz : z<11193-r-v) : combined (eval curve z) r (r+v) z≤budget := by
  simp only [checkRow,Bool.and_eq_true] at h
  apply pointwise_of_cells (fun z c => combined c r (r+v) z≤budget) 0 (11193-r-v) curve h.1 _ z (Nat.zero_le _) hz
  apply cells_mono _ _ _ _ (allCells_sound _ 0 curve h.2)
  intro lo p hp z hzl hzh
  exact piece_sound r (r+v) lo p hp z hzl hzh

end ProximityPrize.SubmissionLower.FinalLedgerChecks6815

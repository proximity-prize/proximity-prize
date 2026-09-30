import ProximityPrize.SubmissionLower.FinalPrefixCheck6815
namespace ProximityPrize.SubmissionLower.FinalPrefixRowsCheck6815
open FinalPrefixCheck6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

structure Entry where
  values : Array ℕ
  mask : ℕ
  deriving Inhabited
def zero : Entry := ⟨#[],1⟩
def coeff (d : Entry) (j : ℕ) : ℕ := (d.values[j]?).getD 0
def phaseAt (d : Entry) (j : ℕ) := coeff d j
def terminalAt (d : Entry) (k : ℕ) := coeff d (k+8)
def present (d : Entry) (k : ℕ) : Bool := d.mask.testBit k
def threshold (th : Array ℕ) (j : ℕ) := MovingFiberSingleCore6815.thresholdAt th j

def check (r v : ℕ) (curve : List FinalCurves6815.Piece) (th : Array ℕ)
    (d prevR prevV : Entry) : Bool :=
  allN (fun j => phaseCheck r v (threshold th (sourceIndex j)) (phaseAt d j) j curve) 8 &&
  allN (fun k => classCheck r v (threshold th 5) (terminalAt d k) k (present d k) curve) 5 &&
  allN (fun j => Nat.ble (coeff prevR j) (coeff d j) && Nat.ble (coeff prevV j) (coeff d j)) 13 &&
  allN (fun k => (!present prevR k || present d k) && (!present prevV k || present d k)) 5

theorem phase_check (r v : ℕ) (curve : List FinalCurves6815.Piece) (th : Array ℕ)
    (d prevR prevV : Entry) (h : check r v curve th d prevR prevV=true)
    (j : ℕ) (hj : j<8) :
    phaseCheck r v (threshold th (sourceIndex j)) (phaseAt d j) j curve=true := by
  simp only [check,Bool.and_eq_true] at h
  exact allN_sound _ 8 h.1.1.1 j hj

theorem class_check (r v : ℕ) (curve : List FinalCurves6815.Piece) (th : Array ℕ)
    (d prevR prevV : Entry) (h : check r v curve th d prevR prevV=true)
    (k : ℕ) (hk : k<5) :
    classCheck r v (threshold th 5) (terminalAt d k) k (present d k) curve=true := by
  simp only [check,Bool.and_eq_true] at h
  exact allN_sound _ 5 h.1.1.2 k hk

theorem coeff_mono (r v : ℕ) (curve : List FinalCurves6815.Piece) (th : Array ℕ)
    (d prevR prevV : Entry) (h : check r v curve th d prevR prevV=true)
    (j : ℕ) (hj : j<13) : coeff prevR j≤coeff d j ∧ coeff prevV j≤coeff d j := by
  simp only [check,Bool.and_eq_true] at h
  have hh := allN_sound _ 13 h.1.2 j hj
  simpa only [Bool.and_eq_true,Nat.ble_eq] using hh

theorem present_mono (r v : ℕ) (curve : List FinalCurves6815.Piece) (th : Array ℕ)
    (d prevR prevV : Entry) (h : check r v curve th d prevR prevV=true)
    (k : ℕ) (hk : k<5) :
    (present prevR k=true → present d k=true) ∧ (present prevV k=true → present d k=true) := by
  simp only [check,Bool.and_eq_true] at h
  have hh := allN_sound _ 5 h.2 k hk
  simp only [Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at hh
  constructor
  · intro hp
    rcases hh.1 with hn | hn
    · simp [hp] at hn
    · exact hn
  · intro hp
    rcases hh.2 with hn | hn
    · simp [hp] at hn
    · exact hn

end ProximityPrize.SubmissionLower.FinalPrefixRowsCheck6815

import ProximityPrize.SubmissionLower.MergedInfra6815_50
import ProximityPrize.SubmissionLower.MergedInfra6815_20
import ProximityPrize.SubmissionLower.MergedInfra6815_13
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.PackingSemantics6815
open PackingCheck6815
open FinalCurves6815
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000

def decodeNatList (radix : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | n+1,c => c%radix :: decodeNatList radix n (c/radix)
def natRow (n bits code : ℕ) : Array ℕ := (decodeNatList (2^bits) n code).toArray
def lookup (rows : ℕ → Array ℕ) (r v : ℕ) := ((rows r)[v]?).getD 0

theorem direct_bellman (Rcap Ycap : ℕ) (own packed : ℕ → Array ℕ)
    (ho : ∀ r, 1≤r → r≤Rcap → (own r).size=Ycap+1-r)
    (hp : ∀ r, r≤Rcap → (packed r).size=Ycap+1-r)
    (hc : ∀ R r, 1≤r → r≤R → R≤Rcap →
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true) :
    AffineFactorAggregate6808.BellmanRows Rcap Ycap (lookup own) (lookup packed) := by
  intro r v R V hr hR hY
  have he : r+R-r=R := by omega
  have hh := hc (r+R) r hr (by omega) hR
  rw [he] at hh
  have h := convolution_sound (own r).toList (packed R).toList (packed (r+R)).toList hh v V
    (by rw [Array.length_toList,ho r hr (by omega)]; omega)
    (by rw [Array.length_toList,hp R (by omega)]; omega)
    (by rw [Array.length_toList,hp (r+R) hR]; omega)
  simpa only [Array.getElem?_toList,lookup] using h

theorem rectangular_bellman (Rcap Vcap : ℕ) (own packed : ℕ → Array ℕ)
    (ho : ∀ r, 1≤r → r≤Rcap → (own r).size=Vcap+1)
    (hp : ∀ r, r≤Rcap → (packed r).size=Vcap+1)
    (hc : ∀ R r, 1≤r → r≤R → R≤Rcap →
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true) :
    RectangularPacking6815.Bellman Rcap Vcap (lookup own) (lookup packed) := by
  intro r v R V hr hR hV
  have he : r+R-r=R := by omega
  have hh := hc (r+R) r hr (by omega) hR
  rw [he] at hh
  have h := convolution_sound (own r).toList (packed R).toList (packed (r+R)).toList hh v V
    (by rw [Array.length_toList,ho r hr (by omega)]; omega)
    (by rw [Array.length_toList,hp R (by omega)]; omega)
    (by rw [Array.length_toList,hp (r+R) hR]; omega)
  simpa only [Array.getElem?_toList,lookup] using h

def checkRow (own packed : ℕ → Array ℕ) (R : ℕ) : Bool :=
  SingletonCertificate6815.allN (fun j => convolution (own (j+1)).toList
    (packed (R-(j+1))).toList (packed R).toList) R

def affineCheck (slope base : ℕ) (curve : List Piece) : Bool :=
  allCells (fun lo p => Nat.ble p.base (slope*lo+base) &&
    Nat.ble (value p lo (p.stop-1)) (slope*(p.stop-1)+base)) 0 curve

theorem affineCheck_sound (slope base finish : ℕ) (curve : List Piece)
    (hv : validFrom finish 0 curve=true) (hc : affineCheck slope base curve=true)
    (z : ℕ) (hz : z<finish) : eval curve z≤slope*z+base := by
  apply pointwise_of_cells (fun z value => value≤slope*z+base) 0 finish curve hv _ z (Nat.zero_le _) hz
  apply cells_mono _ _ 0 curve (allCells_sound _ 0 curve hc)
  intro lo p h x hlox hx
  simp only [Bool.and_eq_true,Nat.ble_eq] at h
  have hh := TriangularAffine6815.shifted_between lo (p.stop-1) x lo 0 p.base base p.slope slope
    le_rfl (Nat.zero_le _) hlox (by omega)
    (by simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.sub_zero,Nat.add_comm] using h.1)
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.2)
  simpa only [value,Nat.sub_zero,Nat.add_comm] using hh

end ProximityPrize.SubmissionLower.PackingSemantics6815
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
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
end MergedPart2

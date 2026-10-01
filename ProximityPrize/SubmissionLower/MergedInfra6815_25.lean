import ProximityPrize.SubmissionLower.MergedInfra6815_3
import ProximityPrize.SubmissionLower.MergedInfra6815_20
import ProximityPrize.SubmissionLower.MergedInfra6815_13
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.FinalLedgerChord6815
open PortfolioChord6815 ExactInitialCharge6815 ExactRemovalPhase6815
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 50000

theorem chord_congr {lo hi : ℕ} {f g : ℕ → ℕ} (hf : Chord lo hi f)
    (he : ∀ z, lo≤z → z≤hi → f z=g z) : Chord lo hi g := by
  intro z hz hh
  simpa only [he z hz hh,he lo le_rfl (hz.trans hh),he hi (hz.trans hh) le_rfl] using hf z hz hh

theorem square_sub (lo hi K : ℕ) (hK : hi≤K) : Chord lo hi (fun z => (K-z)^2) := by
  intro z hz hh
  dsimp only
  rw [show hi-lo=(z-lo)+(hi-z) by omega,
    show K-z=(K-hi)+(hi-z) by omega,
    show K-lo=(K-hi)+(hi-z)+(z-lo) by omega]
  calc
    _≤((z-lo)+(hi-z))*((K-hi)+(hi-z))^2+(z-lo)*(hi-z)*((z-lo)+(hi-z)) := Nat.le_add_right _ _
    _=_ := by ring

theorem sub_affine_eq (lo hi K z : ℕ) (hK : hi≤K) (hz : lo≤z) (hh : z≤hi) :
    (hi-lo)*(K-z)=(hi-z)*(K-lo)+(z-lo)*(K-hi) := by
  rw [show hi-lo=(z-lo)+(hi-z) by omega,
    show K-z=(K-hi)+(hi-z) by omega,
    show K-lo=(K-hi)+(hi-z)+(z-lo) by omega]
  ring

theorem cancel_sub_affine {lo hi K : ℕ} {f : ℕ → ℕ} (a : ℕ) (hK : hi≤K)
    (h : Chord lo hi (fun z => f z+a*(K-z))) : Chord lo hi f := by
  intro z hz hh
  have hc := h z hz hh
  have he := congrArg (fun x => a*x) (sub_affine_eq lo hi K z hK hz hh)
  dsimp only at hc he
  nlinarith only [hc,he]

theorem num_linear (L U S r y t : ℕ) :
    num L U S r y t=num L U S r y 0+tSlope L U S r y*t := by
  rw [num_formula,num_formula]
  unfold tSlope
  ring

theorem num_middle_diagonal (L U S r u : ℕ) :
    num L U S r u u=
      (4*131073*131071*S)*u^2+
      (131073*(2*S+2*131071*r*(L+U)+131071*(2*r-1)*(L+U))+80900*50174*S)*u+
      (131073*r*(L+U)+80900*50174*r*U) := by
  rw [num_formula]
  ring

theorem num_diagonal (L U S u : ℕ) :
    num L U S u u u+(131073*131071*(L+U))*u=
      (4*131073*131071*(L+S+U))*u^2+
      (131073*(L+2*S+U)+80900*50174*(S+U))*u := by
  rw [num_formula]
  cases u with
  | zero => simp
  | succ u =>
    rw [show 2*(u+1)-1=2*u+1 by omega]
    ring

theorem num_linear_chord (L U S r y lo hi K : ℕ) :
    Chord lo hi (fun z => num L U S r y (K-z)) := by
  have h : Chord lo hi (fun z => K-z) := by
    simpa only [Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add] using sub_affine lo hi 0 K 1 0
  apply chord_congr (add (constant lo hi (num L U S r y 0)) (mul_left h (tSlope L U S r y)))
  intro z _ _
  exact (num_linear L U S r y (K-z)).symm

theorem num_middle_chord (L U S r lo hi K : ℕ) (hK : hi≤K) :
    Chord lo hi (fun z => num L U S r (K-z) (K-z)) := by
  have h : Chord lo hi (fun z => K-z) := by
    simpa only [Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add] using sub_affine lo hi 0 K 1 0
  apply chord_congr (add (add (mul_left (square_sub lo hi K hK) (4*131073*131071*S))
    (mul_left h (131073*(2*S+2*131071*r*(L+U)+131071*(2*r-1)*(L+U))+80900*50174*S)))
    (constant lo hi (131073*r*(L+U)+80900*50174*r*U)))
  intro z _ _
  exact (num_middle_diagonal L U S r (K-z)).symm

theorem num_diagonal_chord (L U S lo hi K : ℕ) (hK : hi≤K) :
    Chord lo hi (fun z => num L U S (K-z) (K-z) (K-z)) := by
  have h : Chord lo hi (fun z => K-z) := by
    simpa only [Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add] using sub_affine lo hi 0 K 1 0
  apply cancel_sub_affine (131073*131071*(L+U)) hK
  apply chord_congr (add (mul_left (square_sub lo hi K hK) (4*131073*131071*(L+S+U)))
    (mul_left h (131073*(L+2*S+U)+80900*50174*(S+U))))
  intro z _ _
  exact (num_diagonal L U S (K-z)).symm

def initialNum (r y z : ℕ) : ℕ :=
  let u := 11192-y-z
  num 76330 182 39 (min (50-r) (min (229-y) u)) (min (229-y) u) u
def Mode (r y lo hi mode : ℕ) : Prop :=
  y≤11192 ∧ hi≤11192-y ∧
  if mode=0 then 229-y≤11192-y-hi
  else if mode=1 then min (50-r) (229-y)≤11192-y-hi ∧ 11192-y-lo≤229-y
  else 11192-y-lo≤min (50-r) (229-y)
instance (r y lo hi mode : ℕ) : Decidable (Mode r y lo hi mode) := by unfold Mode; infer_instance

theorem initial_chord (r y lo hi mode : ℕ) (hm : Mode r y lo hi mode) :
    Chord lo hi (initialNum r y) := by
  rcases hm with ⟨_hy,hK,hm⟩
  by_cases h0 : mode=0
  · rw [if_pos h0] at hm
    apply chord_congr (num_linear_chord 76330 182 39 (min (50-r) (229-y)) (229-y) lo hi (11192-y))
    intro z hz hh
    have hu : 229-y≤11192-y-z := by omega
    simp only [initialNum,min_eq_left hu]
  rw [if_neg h0] at hm
  by_cases h1 : mode=1
  · rw [if_pos h1] at hm
    apply chord_congr (num_middle_chord 76330 182 39 (min (50-r) (229-y)) lo hi (11192-y) hK)
    intro z hz hh
    have hu : 11192-y-z≤229-y := by omega
    have he : min (50-r) (11192-y-z)=min (50-r) (229-y) := by omega
    simp only [initialNum,min_eq_right hu,he]
  rw [if_neg h1] at hm
  apply chord_congr (num_diagonal_chord 76330 182 39 lo hi (11192-y) hK)
  intro z hz hh
  have hy : 11192-y-z≤229-y := by omega
  have hr : 11192-y-z≤50-r := by omega
  simp only [initialNum,min_eq_right hy,min_eq_right hr]

open FoldChainPolynomial6815

theorem fold_chord {lo hi : ℕ} {f : ℕ → ℕ} (hf : Chord lo hi f) (y r : ℕ) :
    Chord lo hi (fun z => foldUnit y (f z) r) := by
  by_cases hr : r<2
  · simpa only [foldUnit,if_pos hr] using constant lo hi 9000000000000
  have h2 : Chord lo hi (fun z => foldPiece y (f z) 2) :=
    add (mul_left hf (foldSlope y 2)) (constant lo hi (foldConst y 2))
  have hR : Chord lo hi (fun z => foldPiece y (f z) r) :=
    add (mul_left hf (foldSlope y r)) (constant lo hi (foldConst y r))
  simpa only [foldUnit,if_neg hr] using
    PortfolioChord6815.max (constant lo hi 9000000000000) (PortfolioChord6815.max h2 hR)

def pairLine (r y t : ℕ) := PairCell6815.constant r y/50174-(PairCell6815.slope r y/50174)*t

theorem pair_le (r y t : ℕ) (ht : t≤11193) : PairCell6815.cap r y t≤pairLine r y t := by
  have h := PairCell6815.cap_le_line r y t ht
  unfold PairCell6815.line at h
  unfold pairLine
  omega

def others (r y z : ℕ) : ℕ :=
  r*foldUnit y (y+z) r+(50-r)*foldUnit (229-y) (15421-(y+z)) (50-r)+
    18000000000000+pairLine r y (y+z)

theorem others_chord (r y lo hi : ℕ) : Chord lo hi (others r y) := by
  have hsum : Chord lo hi (fun z => y+z) := by
    simpa only [Nat.one_mul,Nat.add_comm] using affine lo hi 1 y
  have hrem : Chord lo hi (fun z => 15421-(y+z)) := by
    simpa only [Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.add_comm] using sub_affine lo hi 0 15421 1 y
  have hpair : Chord lo hi (fun z => pairLine r y (y+z)) := by
    simpa only [pairLine,Nat.zero_mul,Nat.zero_add,Nat.mul_add,Nat.add_comm] using
      sub_affine lo hi 0 (PairCell6815.constant r y/50174) (PairCell6815.slope r y/50174)
        ((PairCell6815.slope r y/50174)*y)
  exact add (add (add (mul_left (fold_chord hsum y r) r)
      (mul_left (fold_chord hrem (229-y) (50-r)) (50-r)))
    (constant lo hi 18000000000000)) hpair

def cleared (r y start base slope z : ℕ) :=
  50174*(base+slope*(z-start)+others r y z)+initialNum r y z

def combined (cap r y z : ℕ) :=
  cap+initialNum r y z/50174+
    r*foldUnit y (y+z) r+(50-r)*foldUnit (229-y) (15421-(y+z)) (50-r)+
    18000000000000+PairCell6815.cap r y (y+z)

theorem combined_le_cleared (r y start base slope z : ℕ) (ht : y+z≤11193) :
    50174*combined (base+slope*(z-start)) r y z≤cleared r y start base slope z := by
  have hp := pair_le r y (y+z) ht
  have hi := Nat.div_mul_le_self (initialNum r y z) 50174
  unfold combined cleared others
  nlinarith only [hp,hi]

theorem cleared_chord (r y start base slope lo hi mode : ℕ) (hm : Mode r y lo hi mode) :
    Chord lo hi (cleared r y start base slope) := by
  have hsub : Chord lo hi (fun z => z-start) := by
    simpa only [Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add] using sub_affine lo hi 1 0 0 start
  exact add (mul_left (add (add (constant lo hi base) (mul_left hsub slope)) (others_chord r y lo hi)) 50174)
    (initial_chord r y lo hi mode hm)

def Fits (r y start base slope lo hi mode budget : ℕ) : Prop :=
  Mode r y lo hi mode ∧ cleared r y start base slope lo≤50174*budget ∧
    cleared r y start base slope hi≤50174*budget
instance (r y start base slope lo hi mode budget : ℕ) : Decidable (Fits r y start base slope lo hi mode budget) := by
  unfold Fits; infer_instance

theorem fits_between (r y start base slope lo hi mode budget z : ℕ)
    (hf : Fits r y start base slope lo hi mode budget) (hz : lo≤z) (hh : z≤hi) :
    combined (base+slope*(z-start)) r y z≤budget := by
  have h := le_of_endpoints (cleared_chord r y start base slope lo hi mode hf.1)
    (50174*budget) hf.2.1 hf.2.2 z hz hh
  have ht : y+z≤11193 := by have := hf.1.1; have := hf.1.2.1; omega
  exact Nat.le_of_mul_le_mul_left ((combined_le_cleared r y start base slope z ht).trans h) (by decide)

end ProximityPrize.SubmissionLower.FinalLedgerChord6815
end MergedPart0
section MergedPart1
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
end MergedPart1

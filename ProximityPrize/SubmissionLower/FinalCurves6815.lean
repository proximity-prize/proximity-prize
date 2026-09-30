import ProximityPrize.SubmissionLower.TriangularAffine6815
namespace ProximityPrize.SubmissionLower.FinalCurves6815
set_option autoImplicit false
set_option maxHeartbeats 1300000

structure Piece where
  stop : ℕ
  base : ℕ
  slope : ℕ
  deriving DecidableEq

def value (p : Piece) (start z : ℕ) := p.base+p.slope*(z-start)
def evalFrom : ℕ → List Piece → ℕ → ℕ
  | _,[],_ => 0
  | start,p::ps,z => if z<p.stop then value p start z else evalFrom p.stop ps z
def eval (ps : List Piece) (z : ℕ) := evalFrom 0 ps z

def decodeAux (baseRadix slopeRadix : ℕ) : ℕ → ℕ → List Piece
  | 0,_ => []
  | n+1,code =>
      ⟨code%16384,(code/16384)%baseRadix,(code/16384/baseRadix)%slopeRadix⟩ ::
        decodeAux baseRadix slopeRadix n (code/16384/baseRadix/slopeRadix)
def decode (baseBits slopeBits code : ℕ) : List Piece :=
  decodeAux (2^baseBits) (2^slopeBits) (code%65536) (code/65536)

def validFrom (finish : ℕ) : ℕ → List Piece → Bool
  | start,[] => Nat.beq start finish
  | start,p::ps => Nat.blt start p.stop && Nat.ble p.stop finish && validFrom finish p.stop ps
def allCells (test : ℕ → Piece → Bool) : ℕ → List Piece → Bool
  | _,[] => true
  | start,p::ps => test start p && allCells test p.stop ps
def Cells (test : ℕ → Piece → Prop) : ℕ → List Piece → Prop
  | _,[] => True
  | start,p::ps => test start p ∧ Cells test p.stop ps

theorem allCells_sound (test : ℕ → Piece → Bool) (start : ℕ) (ps : List Piece)
    (h : allCells test start ps=true) : Cells (fun s p => test s p=true) start ps := by
  induction ps generalizing start with
  | nil => trivial
  | cons p ps ih =>
    simp only [allCells,Bool.and_eq_true] at h
    exact ⟨h.1,ih _ h.2⟩

theorem cells_mono (p q : ℕ → Piece → Prop) (start : ℕ) (ps : List Piece)
    (h : Cells p start ps) (hpq : ∀ lo piece, p lo piece → q lo piece) : Cells q start ps := by
  induction ps generalizing start with
  | nil => trivial
  | cons piece ps ih => exact ⟨hpq _ _ h.1,ih _ h.2⟩

theorem pointwise_of_cells (property : ℕ → ℕ → Prop) (start finish : ℕ) (ps : List Piece)
    (hv : validFrom finish start ps=true)
    (hc : Cells (fun lo p => ∀ z, lo≤z → z<p.stop → property z (value p lo z)) start ps)
    (z : ℕ) (hz : start≤z) (hf : z<finish) : property z (evalFrom start ps z) := by
  induction ps generalizing start with
  | nil => simp only [validFrom,Nat.beq_eq] at hv; omega
  | cons p ps ih =>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    by_cases h : z<p.stop
    · simpa only [evalFrom,if_pos h] using hc.1 z hz h
    · simpa only [evalFrom,if_neg h] using ih p.stop hv.2 hc.2 (by omega)

def pairCheck (a : Piece) (aStart bStart : ℕ) (b : Piece) : Bool :=
  let lo := max aStart bStart
  let hi := min a.stop b.stop-1
  if lo<min a.stop b.stop then
    Nat.ble (value a aStart lo) (value b bStart lo) &&
      Nat.ble (value a aStart hi) (value b bStart hi)
  else true

theorem pairCheck_sound (a b : Piece) (aStart bStart z : ℕ)
    (h : pairCheck a aStart bStart b=true)
    (ha : aStart≤z) (ha' : z<a.stop) (hb : bStart≤z) (hb' : z<b.stop) :
    value a aStart z≤value b bStart z := by
  have hr : max aStart bStart<min a.stop b.stop := by omega
  simp only [pairCheck,if_pos hr,Bool.and_eq_true,Nat.ble_eq] at h
  exact TriangularAffine6815.shifted_between (max aStart bStart) (min a.stop b.stop-1) z
    aStart bStart a.base b.base a.slope b.slope (le_max_left _ _) (le_max_right _ _)
    (by omega) (by omega) h.1 h.2

def compare (left right : List Piece) : Bool :=
  allCells (fun lo a => allCells (pairCheck a lo) 0 right) 0 left

theorem cell_at (test : ℕ → Piece → Prop) (start finish : ℕ) (ps : List Piece)
    (hv : validFrom finish start ps=true) (hc : Cells test start ps)
    (z : ℕ) (hz : start≤z) (hf : z<finish) :
    ∃ lo p, lo≤z ∧ z<p.stop ∧ evalFrom start ps z=value p lo z ∧ test lo p := by
  induction ps generalizing start with
  | nil => simp only [validFrom,Nat.beq_eq] at hv; omega
  | cons p ps ih =>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    by_cases h : z<p.stop
    · exact ⟨start,p,hz,h,by simp only [evalFrom,if_pos h],hc.1⟩
    · obtain ⟨lo,q,hlo,hhi,he,hq⟩ := ih p.stop hv.2 hc.2 (by omega)
      exact ⟨lo,q,hlo,hhi,by simpa only [evalFrom,if_neg h] using he,hq⟩

theorem compare_sound (left right : List Piece) (finish : ℕ)
    (hl : validFrom finish 0 left=true) (hr : validFrom finish 0 right=true)
    (hc : compare left right=true) (z : ℕ) (hz : z<finish) : eval left z≤eval right z := by
  have hleft := allCells_sound _ 0 left hc
  obtain ⟨lo,a,hlo,hhi,heL,ha⟩ := cell_at _ 0 finish left hl hleft z (Nat.zero_le _) hz
  have hright := allCells_sound _ 0 right ha
  obtain ⟨blo,b,hblo,hbhi,heR,hb⟩ := cell_at _ 0 finish right hr hright z (Nat.zero_le _) hz
  unfold eval
  rw [heL,heR]
  exact pairCheck_sound a b lo blo z hb hlo hhi hblo hbhi

end ProximityPrize.SubmissionLower.FinalCurves6815

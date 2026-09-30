import ProximityPrize.SubmissionLower.FinalRuleCheck6815
namespace ProximityPrize.SubmissionLower.FinalRulesRowCheck6815
open FinalCurves6815 FinalRuleCheck6815
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def decodeAux : ℕ → ℕ → List Piece
  | 0,_ => []
  | n+1,code =>
    let digits := code/262144%1024
    let payload := code/268435456
    ⟨code%16384,code/16384%16,payload%(16^digits)⟩ :: decodeAux n (payload/(16^digits))
def decode (code : ℕ) := decodeAux (code%65536) (code/65536)

def pair (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : Bool :=
  let lo := max rlo start
  let stop := min rule.stop p.stop
  if lo<stop then check r v rule.base rule.slope lo (stop-1) start p else true

def checkRow (r v : ℕ) (curve rules : List Piece) : Bool :=
  validFrom (11193-r-v) 0 rules && allCells (fun lo rule => allCells (pair r v lo rule) 0 curve) 0 rules

def get (ps : List Piece) (i : ℕ) : Piece := (ps[i]?).getD ⟨0,0,0⟩
def startAt (start : ℕ) (ps : List Piece) (i : ℕ) : ℕ :=
  if i=0 then start else (get ps (i-1)).stop

theorem allCells_of_indices (test : ℕ → Piece → Bool) (start : ℕ) (ps : List Piece)
    (h : ∀ i, i<ps.length → test (startAt start ps i) (get ps i)=true) :
    allCells test start ps=true := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    simp only [allCells,Bool.and_eq_true]
    constructor
    · simpa [startAt,get] using h 0 (by simp)
    · apply ih
      intro i hi
      have hh := h (i+1) (by simpa using hi)
      cases i with
      | zero => simpa [startAt,get] using hh
      | succ i => simpa [startAt,get,Nat.add_assoc] using hh

def indexCheck (r v : ℕ) (curve rules : List Piece) (i : ℕ) : Bool :=
  if i<rules.length then allCells (pair r v (startAt 0 rules i) (get rules i)) 0 curve else true
def blockCheck (r v : ℕ) (curve rules : List Piece) (b : ℕ) : Bool :=
  SingletonCertificate6815.allN (fun j => indexCheck r v curve rules (8*b+j)) 8

theorem allN_complete (test : ℕ → Bool) (n : ℕ) (h : ∀ i, i<n → test i=true) :
    SingletonCertificate6815.allN test n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [SingletonCertificate6815.allN,Bool.and_eq_true]
    exact ⟨ih (fun i hi => h i (by omega)),h n (by omega)⟩

theorem block_of_indices (r v : ℕ) (curve rules : List Piece) (b : ℕ)
    (h : ∀ i, i<8 → indexCheck r v curve rules (8*b+i)=true) :
    blockCheck r v curve rules b=true := allN_complete _ 8 h

theorem of_blocks (r v : ℕ) (curve rules : List Piece) (n : ℕ)
    (hv : validFrom (11193-r-v) 0 rules=true) (hn : rules.length≤8*n)
    (hc : ∀ b, b<n → blockCheck r v curve rules b=true) :
    checkRow r v curve rules=true := by
  simp only [checkRow,Bool.and_eq_true]
  refine ⟨hv,allCells_of_indices _ 0 rules ?_⟩
  intro i hi
  have hb : i/8<n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have h := SingletonCertificate6815.allN_sound _ 8 (hc (i/8) hb) (i%8) (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod] at h
  simpa only [indexCheck,if_pos hi] using h

theorem row_sound (r v : ℕ) (curve rules : List Piece)
    (hv : validFrom (11193-r-v) 0 curve=true) (hc : checkRow r v curve rules=true)
    (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (z : ℕ) (ht : r+v+z≤11192) :
    RuleBound r v z (eval curve z) := by
  simp only [checkRow,Bool.and_eq_true] at hc
  obtain ⟨rlo,rule,hrlo,hrhi,_,hrule⟩ := cell_at _ 0 (11193-r-v) rules hc.1
    (allCells_sound _ 0 rules hc.2) z (Nat.zero_le _) (by omega)
  obtain ⟨start,p,hstart,hpstop,he,hp⟩ := cell_at _ 0 (11193-r-v) curve hv
    (allCells_sound _ 0 curve hrule) z (Nat.zero_le _) (by omega)
  have hn : max rlo start<min rule.stop p.stop := by omega
  simp only [pair,if_pos hn] at hp
  have h := check_sound r v rule.base rule.slope (max rlo start) (min rule.stop p.stop-1) start p hp z
    (by omega) (by omega) (le_max_right _ _) hr hR hy ht
  simpa only [eval,he] using h

end ProximityPrize.SubmissionLower.FinalRulesRowCheck6815

import ProximityPrize.SubmissionLower.MovingFiberSingleCore6811
import ProximityPrize.SubmissionLower.MovingFiberLedgerAudit6811
import ProximityPrize.SubmissionLower.MovingFiberThresholdClosed6811
import ProximityPrize.SubmissionLower.MovingFiberPackingData6811S7

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811
open LocatorPhase6800Oracle SecondJetRowIntervals
open Lower80860.PhaseRows Lower80860.ThresholdFast
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def sheetSlope : Nat → Nat
  | 0 => 0 | 1 => 4000000000000 | 2 => 10000000000000 | 3 => 20000000000000
  | 4 => 40000000000000 | 5 => 80000000000000 | 6 => 160000000000000 | _ => 320000000000000

def sheetOwn (j : Nat) : Nat → Nat → Nat :=
  match j with
  | 0 => MovingFiberPackingData6811.S0.own | 1 => MovingFiberPackingData6811.S1.own
  | 2 => MovingFiberPackingData6811.S2.own | 3 => MovingFiberPackingData6811.S3.own
  | 4 => MovingFiberPackingData6811.S4.own | 5 => MovingFiberPackingData6811.S5.own
  | 6 => MovingFiberPackingData6811.S6.own | _ => MovingFiberPackingData6811.S7.own
def sheetPacked (j : Nat) : Nat → Nat → Nat :=
  match j with
  | 0 => MovingFiberPackingData6811.S0.packed | 1 => MovingFiberPackingData6811.S1.packed
  | 2 => MovingFiberPackingData6811.S2.packed | 3 => MovingFiberPackingData6811.S3.packed
  | 4 => MovingFiberPackingData6811.S4.packed | 5 => MovingFiberPackingData6811.S5.packed
  | 6 => MovingFiberPackingData6811.S6.packed | _ => MovingFiberPackingData6811.S7.packed

structure BaseRun where
  stop : Nat
  sheet : Nat
  deriving DecidableEq, Repr
def BaseValid (base : BaseRow) (r v finish : Nat) : Nat → List BaseRun → Prop
  | lo,[] => lo=finish
  | lo,x::xs => lo<x.stop ∧ x.stop≤finish ∧ x.sheet<8 ∧ BaseCell base lo (x.stop-1) ∧
      sheetSlope x.sheet*lo+sheetPacked x.sheet r v ≤ base.evalAt lo ∧
      sheetSlope x.sheet*(x.stop-1)+sheetPacked x.sheet r v ≤ base.evalAt (x.stop-1) ∧
      BaseValid base r v finish x.stop xs
instance (base : BaseRow) (r v finish lo : Nat) (xs : List BaseRun) :
    Decidable (BaseValid base r v finish lo xs) := by
  induction xs generalizing lo with
  | nil => simp only [BaseValid]; infer_instance
  | cons x xs ih => simp only [BaseValid]; infer_instance

theorem base_valid_sound (base : BaseRow) (r v finish lo : Nat) (xs : List BaseRun)
    (h : BaseValid base r v finish lo xs) (z : Nat) (hz : lo≤z) (hzf : z<finish) :
    ∃ j, j<8 ∧ sheetSlope j*z+sheetPacked j r v ≤ base.evalAt z := by
  induction xs generalizing lo with
  | nil => simp only [BaseValid] at h; omega
  | cons x xs ih =>
    rcases h with ⟨hlo,hstop,hj,hcell,h0,h1,hrest⟩
    by_cases hs : z<x.stop
    · refine ⟨x.sheet,hj,?_⟩
      have he := baseAt_affine base lo (x.stop-1) z hcell hz (by omega)
      have he1 := baseAt_affine base lo (x.stop-1) (x.stop-1) hcell (by omega) le_rfl
      have hz' : z=lo+(z-lo) := by omega
      have hi' : x.stop-1=lo+(x.stop-1-lo) := by omega
      have h1' : sheetSlope x.sheet*lo+sheetPacked x.sheet r v+
          sheetSlope x.sheet*(x.stop-1-lo) ≤ base.evalAt lo+baseSlopeAt base lo*(x.stop-1-lo) := by
        rw [he1] at h1
        nlinarith [hi']
      have hh := MovingFiberSingleCore6811.affine_le_between
        (sheetSlope x.sheet*lo+sheetPacked x.sheet r v) (base.evalAt lo)
        (sheetSlope x.sheet) (baseSlopeAt base lo) (z-lo) (x.stop-1-lo) (by omega) h0 h1'
      rw [he]
      nlinarith [hz']
    · exact ih x.stop hrest (by omega)

def ThresholdValid (s : Lower80860.Oracle.SourceNumbers) (r v threshold : Nat)
    (runs : List Lower80860.CompressedBand.Run) : Prop :=
  Lower80860.CompressedBand.Sufficient s r v threshold runs ∨ FastSourceThresholdSufficient s r v threshold
instance (s : Lower80860.Oracle.SourceNumbers) (r v threshold : Nat)
    (runs : List Lower80860.CompressedBand.Run) : Decidable (ThresholdValid s r v threshold runs) := by
  unfold ThresholdValid; infer_instance
theorem threshold_valid_sound (s : Lower80860.Oracle.SourceNumbers) (r v threshold : Nat)
    (runs : List Lower80860.CompressedBand.Run) (h : ThresholdValid s r v threshold runs) :
    FastSourceThresholdSufficient s r v threshold :=
  h.elim (Lower80860.CompressedBand.sufficient_sound s r v threshold runs) id

structure Numbers where
  carrier : MovingFiberSingleCore6811.Carrier
  base : BaseRow
  threshold : Array Nat
  prefixValues : Array Nat
  singletons : List MovingFiberSingleCore6811.Run
  baseChoices : List BaseRun
  phaseRuns : Array (List PhaseRun)
  ledgerRuns : List Lower80860.LedgerAudit.LedgerRun
  thresholdRuns : Array (List Lower80860.CompressedBand.Run)

def defaults : Numbers := ⟨⟨0,0,0,0,0⟩,⟨0,0,0,0,0,[]⟩,#[],#[],[],[],#[],[],#[]⟩
def context (r v : Nat) (current parent : Numbers) : PhaseRowContext :=
  ⟨r,v,current.base,current.threshold,current.prefixValues,parent.prefixValues⟩

def SingleValid (r v : Nat) (row : Numbers) : Prop :=
  row.carrier.Correct r v ∧ ∀ j : Fin 8, MovingFiberSingleCore6811.Cover row.carrier
    (sheetSlope j.val) (sheetOwn j.val r v) r v row.threshold (9276-r-v) 0 row.singletons
instance (r v : Nat) (row : Numbers) : Decidable (SingleValid r v row) := by
  unfold SingleValid; infer_instance
def ThresholdsValid (r v : Nat) (row : Numbers) : Prop :=
  ∀ j : Fin 10, ThresholdValid (Lower80860.TenPhase.sound j.val).source r v
    (Lower80860.PhaseRows.thresholdAt row.threshold j.val) ((row.thresholdRuns[j.val]?).getD [])
instance (r v : Nat) (row : Numbers) : Decidable (ThresholdsValid r v row) := by
  unfold ThresholdsValid; infer_instance

#print axioms base_valid_sound
end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811

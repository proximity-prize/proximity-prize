/- Derived from Lucieno (PR 618), and BitWonka (PR 581) for additional interpolation profiles.
   New 68.32 source parameters, adaptive schedule, cell assignments and integer receipts. Apache-2.0. -/
import ProximityPrize.SubmissionLower.Koala6831ResidualLedger
import ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention
import ProximityPrize.SubmissionLower.Koala6831ResidualLocalTopAvoidance
import ProximityPrize.SubmissionLower.Koala6831MovingShortRetained

set_option Elab.async false

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open Koala6831BenchmarkRetention (commonDiscardBudget retainedSeedBudget)
open Koala6831MovingShortRetained (normalizationBudget)
open Koala6831Protocol (mcaBudget)

def incumbentProfileIds (cell : Cell) : Option (Fin 18 × Fin 18 × Fin 18) :=
  cell.sourceIds

def incumbentCellPrice (cell : Cell) : ℕ :=
  let f := cell.envelope
  match incumbentProfileIds cell with
  | some ids => jetPriceWithCorrections TailCorrections.original f (cellConfig ids)
  | none => rawChargeWithCorrections TailCorrections.original (f.pad 0) f.flag

def incumbentCellTotal (cell : Cell) : ℕ :=
  paid + incumbentCellPrice cell - roomCredit cell.envelope

def incumbentCeiling : ℕ := 272617937942478985

def tangentAllowance : ℕ := 27872095301

def primaryRouteOverrunAllowance : ℕ := 25030294550289

private def incumbentRouteGate (cell : Cell) : Bool :=
  match incumbentProfileIds cell with
  | some ids => jetGatesWithCorrections TailCorrections.original cell.envelope (cellConfig ids) &&
    jetMonotoneWithCorrections TailCorrections.original cell.envelope (cellConfig ids)
  | none => rawGatesWithCorrections TailCorrections.original (cell.envelope.pad 0)

private def checkedIncumbentCell (cell : Cell) : Bool :=
  incumbentRouteGate cell && decide (incumbentCellTotal cell ≤ incumbentCeiling)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
private theorem all_terminalCells_incumbent : terminalCells.all checkedIncumbentCell = true := by
  simp only [terminalCells, List.all_append, Bool.and_eq_true]
  repeat' first | apply And.intro | decide +kernel

theorem incumbentCellTotal_le_of_mem {cell : Cell} (h : cell ∈ terminalCells) :
    incumbentCellTotal cell ≤ incumbentCeiling := by
  have hc := List.all_eq_true.mp all_terminalCells_incumbent cell h
  simp only [checkedIncumbentCell, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.2

theorem incumbentJetGates_of_mem {cell : Cell} (h : cell ∈ terminalCells)
    {ids : Fin 18 × Fin 18 × Fin 18} (hids : incumbentProfileIds cell = some ids) :
    jetGatesWithCorrections TailCorrections.original cell.envelope (cellConfig ids) = true ∧
      jetMonotoneWithCorrections TailCorrections.original cell.envelope (cellConfig ids) = true := by
  have hc := List.all_eq_true.mp all_terminalCells_incumbent cell h
  simp only [checkedIncumbentCell, Bool.and_eq_true, incumbentRouteGate, hids, decide_eq_true_eq] at hc
  exact hc.1

theorem incumbentRawGate_of_mem {cell : Cell} (h : cell ∈ terminalCells)
    (hids : incumbentProfileIds cell = none) :
    rawGatesWithCorrections TailCorrections.original (cell.envelope.pad 0) = true := by
  have hc := List.all_eq_true.mp all_terminalCells_incumbent cell h
  simp only [checkedIncumbentCell, Bool.and_eq_true, incumbentRouteGate, hids, decide_eq_true_eq] at hc
  exact hc.1

theorem incumbentCeiling_with_retained_fees :
    incumbentCeiling + tangentAllowance + primaryRouteOverrunAllowance +
      normalizationBudget ≤ retainedSeedBudget := by
  decide +kernel

end ProximityPrize.SubmissionLower.Koala6831Residual

#print axioms ProximityPrize.SubmissionLower.Koala6831Residual.incumbentCellTotal_le_of_mem

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

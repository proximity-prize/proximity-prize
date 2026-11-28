import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore

set_option autoImplicit false

namespace Research6970.Height2313.Research6969.IndexedReceipts

inductive Action where
  | pair (decision : PairPrices.Decision)
  | three (limit : Option ℕ)
  | excluded (limit : Option ℕ)

structure Receipt where
  row : PairCell.Row
  seed : Fin 18
  action : Action

def Receipt.endWeight (r : Receipt) : Option ℕ :=
  match r.action with
  | .pair d => if PairProof.node d then some d.cutoff else none
  | .three lim | .excluded lim => lim

abbrev Receipt.Done (r : Receipt) : Prop :=
  PairRoute.Done r.seed (PairRoute.of_row r.row r.endWeight)

def Receipt.accepts (r : Receipt) : Bool :=
  match r.action with
  | .pair d => decide (PairPrices.valid r.row r.seed d)
  | .three _ => decide (ThreeRule.check r.row r.seed = true ∧ r.row.graph ≠ 2)
  | .excluded _ => decide ((r.row.cap r.seed).grade < r.row.lowerGrade-r.row.off)

def checked (rows : List Receipt) : Bool := rows.all Receipt.accepts

private theorem proveReceipt (r : Receipt) (paid : r.accepts = true) : r.Done := by
  cases r with
  | mk row seed action =>
    cases action with
    | pair d =>
      have valid : PairPrices.valid row seed d := of_decide_eq_true paid
      exact PairLeaves.paired row d valid _ (fun yes => by simp [Receipt.endWeight, yes])
    | three limit =>
      have valid : ThreeRule.check row seed = true ∧ row.graph ≠ 2 := of_decide_eq_true paid
      exact PairLeaves.three row valid.1 valid.2 limit
    | excluded limit =>
      have valid : (row.cap seed).grade < row.lowerGrade-row.off := of_decide_eq_true paid
      exact PairLeaves.excluded row valid limit

theorem doneAt {rows : List Receipt} (paid : checked rows = true) (i : Fin rows.length) :
    (rows.get i).Done :=
  proveReceipt _ (List.all_eq_true.mp paid _ (List.get_mem rows i))

end Research6970.Height2313.Research6969.IndexedReceipts

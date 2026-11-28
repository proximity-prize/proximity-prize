import ProximityPrize.SubmissionLower.Z6970StockPairRoutes

set_option autoImplicit false

namespace Research6969.StockPairs

def Receipt.endWeight (r : Receipt) : Option ℕ :=
  if PairProof.node r.choice then some r.choice.cutoff else none

abbrev Receipt.Done (r : Receipt) : Prop :=
  PairRoute.Done r.seed (PairRoute.of_row r.row r.endWeight)

theorem doneAt {rows : List Receipt} (paid : checked rows = true) (i : Fin rows.length) :
    (rows.get i).Done :=
  fromCheck (atChecked paid i) _ (fun yes => if_pos yes)

end Research6969.StockPairs

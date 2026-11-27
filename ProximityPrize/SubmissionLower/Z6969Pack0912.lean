import ProximityPrize.SubmissionLower.Z6969Pack0891
import ProximityPrize.SubmissionLower.Witness6966SumO2b

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969WitnessSumO2b
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969WitnessDatO2b

open Low6969GateCell
open scoped BigOperators

def G : Gt := transport Witness6966DatO2b.G
abbrev ws := Witness6966DatO2b.ws
abbrev lv := Witness6966DatO2b.lv
abbrev n := Witness6966DatO2b.n
abbrev rho0 := Witness6966DatO2b.rho0
abbrev amax := Witness6966DatO2b.amax

theorem tabOK : Low6969GateClassTable.tableOK 1 ws = true :=
  (tableOK_transport 1 ws).trans Witness6966DatO2b.tabOK

theorem allOKn : allOK G 1 ws lv 0 n = true :=
  (allOK_transport Witness6966DatO2b.G 1 ws lv 0 n).trans Witness6966DatO2b.allOKn

theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed := by
  simp only [lsum_transport]
  exact Witness6966DatO2b.sumLt.trans_le (by decide)

end Low6969WitnessDatO2b

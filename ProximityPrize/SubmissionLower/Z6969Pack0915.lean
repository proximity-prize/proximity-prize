import ProximityPrize.SubmissionLower.Z6969Pack0891
import ProximityPrize.SubmissionLower.Witness6966SumS1

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969WitnessSumS1
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969WitnessDatS1

open Low6969GateCell
open scoped BigOperators

def G : Gt := transport Witness6966DatS1.G
abbrev ws := Witness6966DatS1.ws
abbrev lv := Witness6966DatS1.lv
abbrev n := Witness6966DatS1.n
abbrev rho0 := Witness6966DatS1.rho0
abbrev amax := Witness6966DatS1.amax

theorem tabOK : Low6969GateClassTable.tableOK 1 ws = true :=
  (tableOK_transport 1 ws).trans Witness6966DatS1.tabOK

theorem allOKn : allOK G 1 ws lv 0 n = true :=
  (allOK_transport Witness6966DatS1.G 1 ws lv 0 n).trans Witness6966DatS1.allOKn

theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed := by
  simp only [lsum_transport]
  exact Witness6966DatS1.sumLt.trans_le (by decide)

end Low6969WitnessDatS1

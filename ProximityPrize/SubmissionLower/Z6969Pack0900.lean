import ProximityPrize.SubmissionLower.Z6969Pack0891
import ProximityPrize.SubmissionLower.Witness6966SumS48x

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969WitnessSumS48x
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969WitnessDatS48x

open Low6969GateCell
open scoped BigOperators

def G : Gt := transport Witness6966DatS48x.G
abbrev ws := Witness6966DatS48x.ws
abbrev lv := Witness6966DatS48x.lv
abbrev n := Witness6966DatS48x.n
abbrev rho0 := Witness6966DatS48x.rho0
abbrev amax := Witness6966DatS48x.amax

theorem tabOK : Low6969GateClassTable.tableOK 1 ws = true :=
  (tableOK_transport 1 ws).trans Witness6966DatS48x.tabOK

theorem allOKn : allOK G 1 ws lv 0 n = true :=
  (allOK_transport Witness6966DatS48x.G 1 ws lv 0 n).trans Witness6966DatS48x.allOKn

theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed := by
  simp only [lsum_transport]
  exact Witness6966DatS48x.sumLt.trans_le (by decide)

end Low6969WitnessDatS48x

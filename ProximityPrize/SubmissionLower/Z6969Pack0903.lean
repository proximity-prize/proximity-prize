import ProximityPrize.SubmissionLower.Z6969Pack0891
import ProximityPrize.SubmissionLower.Witness6966SumETm

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969WitnessSumETm
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969WitnessDatETm

open Low6969GateCell
open scoped BigOperators

def G : Gt := transport Witness6966DatETm.G
abbrev ws := Witness6966DatETm.ws
abbrev lv := Witness6966DatETm.lv
abbrev n := Witness6966DatETm.n
abbrev rho0 := Witness6966DatETm.rho0
abbrev amax := Witness6966DatETm.amax

theorem tabOK : Low6969GateClassTable.tableOK 1 ws = true :=
  (tableOK_transport 1 ws).trans Witness6966DatETm.tabOK

theorem allOKn : allOK G 1 ws lv 0 n = true :=
  (allOK_transport Witness6966DatETm.G 1 ws lv 0 n).trans Witness6966DatETm.allOKn

theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed := by
  simp only [lsum_transport]
  exact Witness6966DatETm.sumLt.trans_le (by decide)

end Low6969WitnessDatETm

import ProximityPrize.SubmissionLower.Z6969Pack0891
import ProximityPrize.SubmissionLower.Witness6966SumETr3x

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969WitnessSumETr3x
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969WitnessDatETr3x

open Low6969GateCell
open scoped BigOperators

def G : Gt := transport Witness6966DatETr3x.G
abbrev ws := Witness6966DatETr3x.ws
abbrev lv := Witness6966DatETr3x.lv
abbrev n := Witness6966DatETr3x.n
abbrev rho0 := Witness6966DatETr3x.rho0
abbrev amax := Witness6966DatETr3x.amax

theorem tabOK : Low6969GateClassTable.tableOK 1 ws = true :=
  (tableOK_transport 1 ws).trans Witness6966DatETr3x.tabOK

theorem allOKn : allOK G 1 ws lv 0 n = true :=
  (allOK_transport Witness6966DatETr3x.G 1 ws lv 0 n).trans Witness6966DatETr3x.allOKn

theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed := by
  simp only [lsum_transport]
  exact Witness6966DatETr3x.sumLt.trans_le (by decide)

end Low6969WitnessDatETr3x

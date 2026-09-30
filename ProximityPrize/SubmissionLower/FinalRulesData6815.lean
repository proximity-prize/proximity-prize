import ProximityPrize.SubmissionLower.FinalRulesRows6815_R01
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R02
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R03
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R04
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R05
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R06
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R07
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R08
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R09
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R10
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R11
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R12
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R13
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R14
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R15
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R16
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R17
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R18
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R19
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R20
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R21
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R22
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R23
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R24
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R25
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R26
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R27
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R28
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R29
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R30
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R31
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R32
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R33
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R34
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R35
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R36
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R37
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R38
import ProximityPrize.SubmissionLower.FinalRulesRows6815_R39
namespace ProximityPrize.SubmissionLower.FinalRulesData6815
open FinalRulesRowCheck6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
def row (r v : ℕ) : List FinalCurves6815.Piece := match r with
  | 1 => FinalRulesRows6815_R01.row v
  | 2 => FinalRulesRows6815_R02.row v
  | 3 => FinalRulesRows6815_R03.row v
  | 4 => FinalRulesRows6815_R04.row v
  | 5 => FinalRulesRows6815_R05.row v
  | 6 => FinalRulesRows6815_R06.row v
  | 7 => FinalRulesRows6815_R07.row v
  | 8 => FinalRulesRows6815_R08.row v
  | 9 => FinalRulesRows6815_R09.row v
  | 10 => FinalRulesRows6815_R10.row v
  | 11 => FinalRulesRows6815_R11.row v
  | 12 => FinalRulesRows6815_R12.row v
  | 13 => FinalRulesRows6815_R13.row v
  | 14 => FinalRulesRows6815_R14.row v
  | 15 => FinalRulesRows6815_R15.row v
  | 16 => FinalRulesRows6815_R16.row v
  | 17 => FinalRulesRows6815_R17.row v
  | 18 => FinalRulesRows6815_R18.row v
  | 19 => FinalRulesRows6815_R19.row v
  | 20 => FinalRulesRows6815_R20.row v
  | 21 => FinalRulesRows6815_R21.row v
  | 22 => FinalRulesRows6815_R22.row v
  | 23 => FinalRulesRows6815_R23.row v
  | 24 => FinalRulesRows6815_R24.row v
  | 25 => FinalRulesRows6815_R25.row v
  | 26 => FinalRulesRows6815_R26.row v
  | 27 => FinalRulesRows6815_R27.row v
  | 28 => FinalRulesRows6815_R28.row v
  | 29 => FinalRulesRows6815_R29.row v
  | 30 => FinalRulesRows6815_R30.row v
  | 31 => FinalRulesRows6815_R31.row v
  | 32 => FinalRulesRows6815_R32.row v
  | 33 => FinalRulesRows6815_R33.row v
  | 34 => FinalRulesRows6815_R34.row v
  | 35 => FinalRulesRows6815_R35.row v
  | 36 => FinalRulesRows6815_R36.row v
  | 37 => FinalRulesRows6815_R37.row v
  | 38 => FinalRulesRows6815_R38.row v
  | 39 => FinalRulesRows6815_R39.row v
  | _ => []
theorem checked (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) : checkRow r v (FinalLedgerData6815.row r v) (row r v)=true := by
  interval_cases r
  · exact FinalRulesRows6815_R01.checked v (by omega)
  · exact FinalRulesRows6815_R02.checked v (by omega)
  · exact FinalRulesRows6815_R03.checked v (by omega)
  · exact FinalRulesRows6815_R04.checked v (by omega)
  · exact FinalRulesRows6815_R05.checked v (by omega)
  · exact FinalRulesRows6815_R06.checked v (by omega)
  · exact FinalRulesRows6815_R07.checked v (by omega)
  · exact FinalRulesRows6815_R08.checked v (by omega)
  · exact FinalRulesRows6815_R09.checked v (by omega)
  · exact FinalRulesRows6815_R10.checked v (by omega)
  · exact FinalRulesRows6815_R11.checked v (by omega)
  · exact FinalRulesRows6815_R12.checked v (by omega)
  · exact FinalRulesRows6815_R13.checked v (by omega)
  · exact FinalRulesRows6815_R14.checked v (by omega)
  · exact FinalRulesRows6815_R15.checked v (by omega)
  · exact FinalRulesRows6815_R16.checked v (by omega)
  · exact FinalRulesRows6815_R17.checked v (by omega)
  · exact FinalRulesRows6815_R18.checked v (by omega)
  · exact FinalRulesRows6815_R19.checked v (by omega)
  · exact FinalRulesRows6815_R20.checked v (by omega)
  · exact FinalRulesRows6815_R21.checked v (by omega)
  · exact FinalRulesRows6815_R22.checked v (by omega)
  · exact FinalRulesRows6815_R23.checked v (by omega)
  · exact FinalRulesRows6815_R24.checked v (by omega)
  · exact FinalRulesRows6815_R25.checked v (by omega)
  · exact FinalRulesRows6815_R26.checked v (by omega)
  · exact FinalRulesRows6815_R27.checked v (by omega)
  · exact FinalRulesRows6815_R28.checked v (by omega)
  · exact FinalRulesRows6815_R29.checked v (by omega)
  · exact FinalRulesRows6815_R30.checked v (by omega)
  · exact FinalRulesRows6815_R31.checked v (by omega)
  · exact FinalRulesRows6815_R32.checked v (by omega)
  · exact FinalRulesRows6815_R33.checked v (by omega)
  · exact FinalRulesRows6815_R34.checked v (by omega)
  · exact FinalRulesRows6815_R35.checked v (by omega)
  · exact FinalRulesRows6815_R36.checked v (by omega)
  · exact FinalRulesRows6815_R37.checked v (by omega)
  · exact FinalRulesRows6815_R38.checked v (by omega)
  · exact FinalRulesRows6815_R39.checked v (by omega)
theorem rule_bound (r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    FinalRuleCheck6815.RuleBound r v z (FinalLedgerData6815.cap r v z) :=
  row_sound r v _ _ (FinalPrefixSound6815.curve_valid r v hr hR hy) (checked r v hr hR hy) hr hR hy z ht
end ProximityPrize.SubmissionLower.FinalRulesData6815

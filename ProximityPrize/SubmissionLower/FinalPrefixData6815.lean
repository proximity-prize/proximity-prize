import ProximityPrize.SubmissionLower.FinalPrefixRows6815_R39
namespace ProximityPrize.SubmissionLower.FinalPrefixData6815
open FinalPrefixRowsCheck6815 FinalPrefixRows6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
def row (r v : ℕ) : Entry := match r with
  | 1 => row1 v
  | 2 => row2 v
  | 3 => row3 v
  | 4 => row4 v
  | 5 => row5 v
  | 6 => row6 v
  | 7 => row7 v
  | 8 => row8 v
  | 9 => row9 v
  | 10 => row10 v
  | 11 => row11 v
  | 12 => row12 v
  | 13 => row13 v
  | 14 => row14 v
  | 15 => row15 v
  | 16 => row16 v
  | 17 => row17 v
  | 18 => row18 v
  | 19 => row19 v
  | 20 => row20 v
  | 21 => row21 v
  | 22 => row22 v
  | 23 => row23 v
  | 24 => row24 v
  | 25 => row25 v
  | 26 => row26 v
  | 27 => row27 v
  | 28 => row28 v
  | 29 => row29 v
  | 30 => row30 v
  | 31 => row31 v
  | 32 => row32 v
  | 33 => row33 v
  | 34 => row34 v
  | 35 => row35 v
  | 36 => row36 v
  | 37 => row37 v
  | 38 => row38 v
  | 39 => row39 v
  | _ => zero
theorem checked (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hY : r+v≤182) :
    check r v (FinalLedgerData6815.row r v) (thresholds (SingletonData6815.row r v)) (row r v) (row (r-1) v) (if v=0 then zero else row r (v-1))=true := by
  interval_cases r
  · exact checked1 v (by omega)
  · exact checked2 v (by omega)
  · exact checked3 v (by omega)
  · exact checked4 v (by omega)
  · exact checked5 v (by omega)
  · exact checked6 v (by omega)
  · exact checked7 v (by omega)
  · exact checked8 v (by omega)
  · exact checked9 v (by omega)
  · exact checked10 v (by omega)
  · exact checked11 v (by omega)
  · exact checked12 v (by omega)
  · exact checked13 v (by omega)
  · exact checked14 v (by omega)
  · exact checked15 v (by omega)
  · exact checked16 v (by omega)
  · exact checked17 v (by omega)
  · exact checked18 v (by omega)
  · exact checked19 v (by omega)
  · exact checked20 v (by omega)
  · exact checked21 v (by omega)
  · exact checked22 v (by omega)
  · exact checked23 v (by omega)
  · exact checked24 v (by omega)
  · exact checked25 v (by omega)
  · exact checked26 v (by omega)
  · exact checked27 v (by omega)
  · exact checked28 v (by omega)
  · exact checked29 v (by omega)
  · exact checked30 v (by omega)
  · exact checked31 v (by omega)
  · exact checked32 v (by omega)
  · exact checked33 v (by omega)
  · exact checked34 v (by omega)
  · exact checked35 v (by omega)
  · exact checked36 v (by omega)
  · exact checked37 v (by omega)
  · exact checked38 v (by omega)
  · exact checked39 v (by omega)
end ProximityPrize.SubmissionLower.FinalPrefixData6815

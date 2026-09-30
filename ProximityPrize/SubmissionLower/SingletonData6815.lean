import ProximityPrize.SubmissionLower.SingletonRows6815_R39
namespace ProximityPrize.SubmissionLower.SingletonData6815
open SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
def row (r v : ℕ) : Row := match r with
  | 1 => SingletonRows6815_R01.row v
  | 2 => SingletonRows6815_R02.row v
  | 3 => SingletonRows6815_R03.row v
  | 4 => SingletonRows6815_R04.row v
  | 5 => SingletonRows6815_R05.row v
  | 6 => SingletonRows6815_R06.row v
  | 7 => SingletonRows6815_R07.row v
  | 8 => SingletonRows6815_R08.row v
  | 9 => SingletonRows6815_R09.row v
  | 10 => SingletonRows6815_R10.row v
  | 11 => SingletonRows6815_R11.row v
  | 12 => SingletonRows6815_R12.row v
  | 13 => SingletonRows6815_R13.row v
  | 14 => SingletonRows6815_R14.row v
  | 15 => SingletonRows6815_R15.row v
  | 16 => SingletonRows6815_R16.row v
  | 17 => SingletonRows6815_R17.row v
  | 18 => SingletonRows6815_R18.row v
  | 19 => SingletonRows6815_R19.row v
  | 20 => SingletonRows6815_R20.row v
  | 21 => SingletonRows6815_R21.row v
  | 22 => SingletonRows6815_R22.row v
  | 23 => SingletonRows6815_R23.row v
  | 24 => SingletonRows6815_R24.row v
  | 25 => SingletonRows6815_R25.row v
  | 26 => SingletonRows6815_R26.row v
  | 27 => SingletonRows6815_R27.row v
  | 28 => SingletonRows6815_R28.row v
  | 29 => SingletonRows6815_R29.row v
  | 30 => SingletonRows6815_R30.row v
  | 31 => SingletonRows6815_R31.row v
  | 32 => SingletonRows6815_R32.row v
  | 33 => SingletonRows6815_R33.row v
  | 34 => SingletonRows6815_R34.row v
  | 35 => SingletonRows6815_R35.row v
  | 36 => SingletonRows6815_R36.row v
  | 37 => SingletonRows6815_R37.row v
  | 38 => SingletonRows6815_R38.row v
  | 39 => SingletonRows6815_R39.row v
  | _ => default
theorem checked (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hY : r+v≤182) : check r v (row r v)=true := by
  interval_cases r
  · exact SingletonRows6815_R01.checked v (by omega)
  · exact SingletonRows6815_R02.checked v (by omega)
  · exact SingletonRows6815_R03.checked v (by omega)
  · exact SingletonRows6815_R04.checked v (by omega)
  · exact SingletonRows6815_R05.checked v (by omega)
  · exact SingletonRows6815_R06.checked v (by omega)
  · exact SingletonRows6815_R07.checked v (by omega)
  · exact SingletonRows6815_R08.checked v (by omega)
  · exact SingletonRows6815_R09.checked v (by omega)
  · exact SingletonRows6815_R10.checked v (by omega)
  · exact SingletonRows6815_R11.checked v (by omega)
  · exact SingletonRows6815_R12.checked v (by omega)
  · exact SingletonRows6815_R13.checked v (by omega)
  · exact SingletonRows6815_R14.checked v (by omega)
  · exact SingletonRows6815_R15.checked v (by omega)
  · exact SingletonRows6815_R16.checked v (by omega)
  · exact SingletonRows6815_R17.checked v (by omega)
  · exact SingletonRows6815_R18.checked v (by omega)
  · exact SingletonRows6815_R19.checked v (by omega)
  · exact SingletonRows6815_R20.checked v (by omega)
  · exact SingletonRows6815_R21.checked v (by omega)
  · exact SingletonRows6815_R22.checked v (by omega)
  · exact SingletonRows6815_R23.checked v (by omega)
  · exact SingletonRows6815_R24.checked v (by omega)
  · exact SingletonRows6815_R25.checked v (by omega)
  · exact SingletonRows6815_R26.checked v (by omega)
  · exact SingletonRows6815_R27.checked v (by omega)
  · exact SingletonRows6815_R28.checked v (by omega)
  · exact SingletonRows6815_R29.checked v (by omega)
  · exact SingletonRows6815_R30.checked v (by omega)
  · exact SingletonRows6815_R31.checked v (by omega)
  · exact SingletonRows6815_R32.checked v (by omega)
  · exact SingletonRows6815_R33.checked v (by omega)
  · exact SingletonRows6815_R34.checked v (by omega)
  · exact SingletonRows6815_R35.checked v (by omega)
  · exact SingletonRows6815_R36.checked v (by omega)
  · exact SingletonRows6815_R37.checked v (by omega)
  · exact SingletonRows6815_R38.checked v (by omega)
  · exact SingletonRows6815_R39.checked v (by omega)
def curve (r v : ℕ) := (row r v).curve
def cap (r v z : ℕ) := FinalCurves6815.eval (curve r v) z
end ProximityPrize.SubmissionLower.SingletonData6815

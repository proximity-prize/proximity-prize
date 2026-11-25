import ProximityPrize.SubmissionLower.Gate61DatLO3T0
import ProximityPrize.SubmissionLower.Gate61DatLO3M0
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatLO3
open Gate61Cell
theorem tabOK : Gate61ClassTable.tableOK 1 ws = true := tableOK_of_all ws 1 0 (by simpa [ws] using (tabAll_add 1 ws 0 176 4 (tabAll_add 1 ws 0 168 8 (tabAll_add 1 ws 0 160 8 (tabAll_add 1 ws 0 152 8 (tabAll_add 1 ws 0 144 8 (tabAll_add 1 ws 0 136 8 (tabAll_add 1 ws 0 128 8 (tabAll_add 1 ws 0 120 8 (tabAll_add 1 ws 0 112 8 (tabAll_add 1 ws 0 104 8 (tabAll_add 1 ws 0 96 8 (tabAll_add 1 ws 0 88 8 (tabAll_add 1 ws 0 80 8 (tabAll_add 1 ws 0 72 8 (tabAll_add 1 ws 0 64 8 (tabAll_add 1 ws 0 56 8 (tabAll_add 1 ws 0 48 8 (tabAll_add 1 ws 0 40 8 (tabAll_add 1 ws 0 32 8 (tabAll_add 1 ws 0 24 8 (tabAll_add 1 ws 0 16 8 (tabAll_add 1 ws 0 8 8 (tabAll_add 1 ws 0 0 8 (tabAll_nil 1 ws 0) T0) T1) T2) T3) T4) T5) T6) T7) T8) T9) T10) T11) T12) T13) T14) T15) T16) T17) T18) T19) T20) T21) T22))
theorem allOKn : allOK G 1 ws lv 0 n = true := allOK_add G 1 ws lv 0 96 84 (allOK_add G 1 ws lv 0 81 15 (allOK_add G 1 ws lv 0 77 4 (allOK_add G 1 ws lv 0 75 2 (allOK_add G 1 ws lv 0 73 2 (allOK_add G 1 ws lv 0 67 6 (allOK_add G 1 ws lv 0 61 6 (allOK_add G 1 ws lv 0 54 7 (allOK_add G 1 ws lv 0 40 14 (allOK_add G 1 ws lv 0 0 40 (allOK_nil G 1 ws lv 0) C0) C1) C2) C3) C4) C5) C6) C7) C8) C9
end Gate61DatLO3

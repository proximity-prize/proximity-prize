import ProximityPrize.SubmissionLower.Gate61DatLODT0
import ProximityPrize.SubmissionLower.Gate61DatLODM0
import ProximityPrize.SubmissionLower.Gate61DatLODM1
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatLOD
open Gate61Cell
theorem tabOK : Gate61ClassTable.tableOK 1 ws = true := tableOK_of_all ws 1 0 (by simpa [ws] using (tabAll_add 1 ws 0 176 7 (tabAll_add 1 ws 0 168 8 (tabAll_add 1 ws 0 160 8 (tabAll_add 1 ws 0 152 8 (tabAll_add 1 ws 0 144 8 (tabAll_add 1 ws 0 136 8 (tabAll_add 1 ws 0 128 8 (tabAll_add 1 ws 0 120 8 (tabAll_add 1 ws 0 112 8 (tabAll_add 1 ws 0 104 8 (tabAll_add 1 ws 0 96 8 (tabAll_add 1 ws 0 88 8 (tabAll_add 1 ws 0 80 8 (tabAll_add 1 ws 0 72 8 (tabAll_add 1 ws 0 64 8 (tabAll_add 1 ws 0 56 8 (tabAll_add 1 ws 0 48 8 (tabAll_add 1 ws 0 40 8 (tabAll_add 1 ws 0 32 8 (tabAll_add 1 ws 0 24 8 (tabAll_add 1 ws 0 16 8 (tabAll_add 1 ws 0 8 8 (tabAll_add 1 ws 0 0 8 (tabAll_nil 1 ws 0) T0) T1) T2) T3) T4) T5) T6) T7) T8) T9) T10) T11) T12) T13) T14) T15) T16) T17) T18) T19) T20) T21) T22))
theorem allOKn : allOK G 1 ws lv 0 n = true := allOK_add G 1 ws lv 0 100 83 (allOK_add G 1 ws lv 0 81 19 (allOK_add G 1 ws lv 0 76 5 (allOK_add G 1 ws lv 0 74 2 (allOK_add G 1 ws lv 0 72 2 (allOK_add G 1 ws lv 0 69 3 (allOK_add G 1 ws lv 0 68 1 (allOK_add G 1 ws lv 0 67 1 (allOK_add G 1 ws lv 0 66 1 (allOK_add G 1 ws lv 0 65 1 (allOK_add G 1 ws lv 0 64 1 (allOK_add G 1 ws lv 0 63 1 (allOK_add G 1 ws lv 0 60 3 (allOK_add G 1 ws lv 0 53 7 (allOK_add G 1 ws lv 0 43 10 (allOK_add G 1 ws lv 0 34 9 (allOK_add G 1 ws lv 0 25 9 (allOK_add G 1 ws lv 0 14 11 (allOK_add G 1 ws lv 0 0 14 (allOK_nil G 1 ws lv 0) C0) C1) C2) C3) C4) C5) C6) C7) C8) C9) C10) C11) C12) C13) C14) C15) C16) C17) C18
end Gate61DatLOD

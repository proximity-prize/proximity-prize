import ProximityPrize.SubmissionLower.Gate61DatLODDefs
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatLOD
open Gate61Cell
theorem C0 : allOK G 1 ws lv 0 14 = true := by decide +kernel
theorem C1 : allOK G 1 ws lv 14 11 = true := by decide +kernel
theorem C2 : allOK G 1 ws lv 25 9 = true := by decide +kernel
theorem C3 : allOK G 1 ws lv 34 9 = true := by decide +kernel
theorem C4 : allOK G 1 ws lv 43 10 = true := by decide +kernel
theorem C5 : allOK G 1 ws lv 53 7 = true := by decide +kernel
theorem C6 : allOK G 1 ws lv 60 3 = true := by decide +kernel
theorem C8 : allOK G 1 ws lv 64 1 = true := by decide +kernel
theorem C9 : allOK G 1 ws lv 65 1 = true := by decide +kernel
theorem C10 : allOK G 1 ws lv 66 1 = true := by decide +kernel
theorem C11 : allOK G 1 ws lv 67 1 = true := by decide +kernel
theorem C12 : allOK G 1 ws lv 68 1 = true := by decide +kernel
theorem C13 : allOK G 1 ws lv 69 3 = true := by decide +kernel
theorem C14 : allOK G 1 ws lv 72 2 = true := by decide +kernel
theorem C15 : allOK G 1 ws lv 74 2 = true := by decide +kernel
theorem C16 : allOK G 1 ws lv 76 5 = true := by decide +kernel
theorem C17 : allOK G 1 ws lv 81 19 = true := by decide +kernel
theorem C18 : allOK G 1 ws lv 100 83 = true := by decide +kernel
end Gate61DatLOD

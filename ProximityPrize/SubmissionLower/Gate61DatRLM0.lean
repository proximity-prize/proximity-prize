import ProximityPrize.SubmissionLower.Gate61DatRLDefs
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatRL
open Gate61Cell
theorem C0 : allOK G 1 ws lv 0 30 = true := by decide +kernel
theorem C1 : allOK G 1 ws lv 30 16 = true := by decide +kernel
theorem C2 : allOK G 1 ws lv 46 8 = true := by decide +kernel
theorem C3 : allOK G 1 ws lv 54 2 = true := by decide +kernel
theorem C4 : allOK G 1 ws lv 56 1 = true := by decide +kernel
theorem C5 : allOK G 1 ws lv 57 1 = true := by decide +kernel
theorem C6 : allOK G 1 ws lv 58 1 = true := by decide +kernel
theorem C7 : allOK G 1 ws lv 59 1 = true := by decide +kernel
theorem C8 : allOK G 1 ws lv 60 1 = true := by decide +kernel
theorem C9 : allOK G 1 ws lv 61 1 = true := by decide +kernel
theorem C10 : allOK G 1 ws lv 62 1 = true := by decide +kernel
theorem C11 : allOK G 1 ws lv 63 1 = true := by decide +kernel
theorem C12 : allOK G 1 ws lv 64 1 = true := by decide +kernel
theorem C13 : allOK G 1 ws lv 65 1 = true := by decide +kernel
theorem C14 : allOK G 1 ws lv 66 1 = true := by decide +kernel
theorem C15 : allOK G 1 ws lv 67 1 = true := by decide +kernel
theorem C16 : allOK G 1 ws lv 68 1 = true := by decide +kernel
theorem C17 : allOK G 1 ws lv 69 2 = true := by decide +kernel
theorem C18 : allOK G 1 ws lv 71 3 = true := by decide +kernel
theorem C19 : allOK G 1 ws lv 74 2 = true := by decide +kernel
theorem C20 : allOK G 1 ws lv 76 2 = true := by decide +kernel
theorem C21 : allOK G 1 ws lv 78 2 = true := by decide +kernel
theorem C22 : allOK G 1 ws lv 80 3 = true := by decide +kernel
theorem C23 : allOK G 1 ws lv 83 4 = true := by decide +kernel
theorem C24 : allOK G 1 ws lv 87 4 = true := by decide +kernel
theorem C25 : allOK G 1 ws lv 91 12 = true := by decide +kernel
theorem C26 : allOK G 1 ws lv 103 106 = true := by decide +kernel
end Gate61DatRL

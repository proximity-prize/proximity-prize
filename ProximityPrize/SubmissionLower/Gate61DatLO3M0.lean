import ProximityPrize.SubmissionLower.Gate61DatLO3Defs
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatLO3
open Gate61Cell
theorem C0 : allOK G 1 ws lv 0 40 = true := by decide +kernel
theorem C1 : allOK G 1 ws lv 40 14 = true := by decide +kernel
theorem C2 : allOK G 1 ws lv 54 7 = true := by decide +kernel
theorem C3 : allOK G 1 ws lv 61 6 = true := by decide +kernel
theorem C4 : allOK G 1 ws lv 67 6 = true := by decide +kernel
theorem C5 : allOK G 1 ws lv 73 2 = true := by decide +kernel
theorem C6 : allOK G 1 ws lv 75 2 = true := by decide +kernel
theorem C7 : allOK G 1 ws lv 77 4 = true := by decide +kernel
theorem C8 : allOK G 1 ws lv 81 15 = true := by decide +kernel
theorem C9 : allOK G 1 ws lv 96 84 = true := by decide +kernel
end Gate61DatLO3

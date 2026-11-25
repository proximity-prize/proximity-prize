import ProximityPrize.SubmissionLower.Gate61DatLOBDefs
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatLOB
open Gate61Cell
theorem C79 : allOK G 1 ws lv 88 2 = true := by decide +kernel
theorem C80 : allOK G 1 ws lv 90 3 = true := by decide +kernel
theorem C81 : allOK G 1 ws lv 93 7 = true := by decide +kernel
theorem C82 : allOK G 1 ws lv 100 21 = true := by decide +kernel
theorem C83 : allOK G 1 ws lv 121 98 = true := by decide +kernel
end Gate61DatLOB

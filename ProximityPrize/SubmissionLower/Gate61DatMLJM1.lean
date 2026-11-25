import ProximityPrize.SubmissionLower.Gate61DatMLJDefs
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatMLJ
open Gate61Cell
theorem C61 : allOK G 1 ws lv 89 1 = true := by decide +kernel
theorem C62 : allOK G 1 ws lv 90 1 = true := by decide +kernel
theorem C63 : allOK G 1 ws lv 91 1 = true := by decide +kernel
theorem C64 : allOK G 1 ws lv 92 1 = true := by decide +kernel
theorem C65 : allOK G 1 ws lv 93 2 = true := by decide +kernel
theorem C66 : allOK G 1 ws lv 95 4 = true := by decide +kernel
theorem C67 : allOK G 1 ws lv 99 10 = true := by decide +kernel
theorem C68 : allOK G 1 ws lv 109 45 = true := by decide +kernel
theorem C69 : allOK G 1 ws lv 154 72 = true := by decide +kernel
end Gate61DatMLJ

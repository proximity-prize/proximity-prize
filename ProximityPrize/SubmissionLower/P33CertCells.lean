/- Old-style (common small support) composition cells: none at 68.35 / refined run; the refined cells are in
`P33RCertCells`. The old path (`certCheck`, `composition_card_le`) is kept compiled and usable. -/
import ProximityPrize.SubmissionLower.P33Check

set_option Elab.async false

namespace ProximityPrize
namespace SubmissionLower
namespace P33
set_option autoImplicit false
def certCells : List P33.CertCell := []
theorem certCells_ok : certCells.all P33.certCheck = true := by decide
end P33
end SubmissionLower
end ProximityPrize

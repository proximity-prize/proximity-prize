import ProximityPrize.SubmissionLower.Z6970GateLeadingChecked
import ProximityPrize.SubmissionLower.Z6970GateLeadingPrefix
import ProximityPrize.SubmissionLower.Z6970GateLeadingInvoice

set_option autoImplicit false
set_option Elab.async false

namespace Gate6970Leading
open Gate6966Cell (Lv)

theorem actual_mass (lv : Lv) (lo n : ℕ) :
    mass («prefix» stairs) lv lo n = ExpandedGate6970.H2307Numeric.mass lv lo n :=
  mass_eq («prefix» stairs) (prefix_eq stairs stairs_checked) lv lo n

end Gate6970Leading

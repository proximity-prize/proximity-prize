import ProximityPrize.SubmissionLower.Z6970ExpandedPivotCore
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedTaper6970
open Low48PrimaryPivot (twiceTri)
open ExpandedPivotOpt6970 (Column Triple columnPoint)

def triangle (z : Column) : ℤ :=
  let p := columnPoint z
  if p.index ≤ 1679 then
    twiceTri (3000 + (p.index : ℤ) - (p.contact : ℤ) - 1679) -
      twiceTri (3000 + (p.index : ℤ) - (p.contact : ℤ) - 3514)
  else 0

end ExpandedTaper6970

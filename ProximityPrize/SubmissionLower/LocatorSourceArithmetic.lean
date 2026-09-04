import ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorSourceArithmetic. -/
section PackedLocator_LocatorSourceArithmetic
namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
theorem kernelAmbient_nullity:
    coefficientCount 48970710 131071 130000 81 -
      262144 * localRankBound 270 130000 81=303286218157264:=
  LocatorArithmetic.kernelC_nullity
end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
end PackedLocator_LocatorSourceArithmetic

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier60 : True := by trivial
end ProximityPrize.SubmissionLower


import ProximityPrize.SubmissionLower.AnchorTopFactor
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace AnchorBlock82190
open K1_13 K1_13_1_1 MvPolynomial
open SoundnessAnchor (Powers)
open private factor_band factor_order factor_ne from ProximityPrize.SubmissionLower.AnchorTopFactor
open private smallContact smallContact_order from ProximityPrize.SubmissionLower.Fast054
noncomputable section

/-- Truncate a homogeneous band after the change of jet coordinates. -/
def blockAt (d s : ℕ) (g : ℤ) : bandSpace d (-g) 48 12 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _

end
end AnchorBlock82190

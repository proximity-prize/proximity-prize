import ProximityPrize.SubmissionLower.PhasePotential6815
namespace ProximityPrize.SubmissionLower.BalancedPhasePotential6815
open RCN260 AsymmetricHelper PhasePotential6815
set_option autoImplicit false
set_option maxHeartbeats 1400000

def CoefficientsFit (L U S Rcap Ycap Tcap qt qy qr : ℕ) : Prop :=
  2*131073*131071*((S:ℤ)*Ycap+(U:ℤ)*Rcap)+131073*((S:ℤ)-131071*U)≤50174*(qt:ℤ) ∧
  2*131073*131071*((L:ℤ)*Rcap+(S:ℤ)*Tcap)+131073*((S:ℤ)-131071*L)+80900*50174*S≤50174*(qy:ℤ) ∧
  2*131073*131071*((L:ℤ)*Ycap+(U:ℤ)*Tcap)+131073*((L:ℤ)+U)+80900*50174*U≤50174*(qr:ℤ)
instance (L U S Rcap Ycap Tcap qt qy qr : ℕ) : Decidable (CoefficientsFit L U S Rcap Ycap Tcap qt qy qr) := by
  unfold CoefficientsFit; infer_instance

theorem box_product (x y capX capY : ℤ) (hx : 0≤x) (hy : 0≤y) (hX : x≤capX) (hY : y≤capY) :
    2*x*y≤capX*y+capY*x := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) hy,mul_nonneg (sub_nonneg.mpr hY) hx]

theorem count_le (L U S Rcap Ycap Tcap qt qy qr r y t : ℕ)
    (hf : CoefficientsFit L U S Rcap Ycap Tcap qt qy qr)
    (hr : 1≤r) (hR : r≤Rcap) (hY : y≤Ycap) (hT : t≤Tcap) :
    leftRegularCountCap (pair L U S r y t)≤qt*t+qy*y+qr*r := by
  have hry := box_product r y Rcap Ycap (by positivity) (by positivity)
    (by exact_mod_cast hR) (by exact_mod_cast hY)
  have hrt := box_product r t Rcap Tcap (by positivity) (by positivity)
    (by exact_mod_cast hR) (by exact_mod_cast hT)
  have hty := box_product t y Tcap Ycap (by positivity) (by positivity)
    (by exact_mod_cast hT) (by exact_mod_cast hY)
  have h1 := mul_le_mul_of_nonneg_left hry (show (0:ℤ)≤2*131073*131071*L by positivity)
  have h2 := mul_le_mul_of_nonneg_left hrt (show (0:ℤ)≤2*131073*131071*U by positivity)
  have h3 := mul_le_mul_of_nonneg_left hty (show (0:ℤ)≤2*131073*131071*S by positivity)
  have h4 := mul_le_mul_of_nonneg_right hf.1 (show (0:ℤ)≤t by positivity)
  have h5 := mul_le_mul_of_nonneg_right hf.2.1 (show (0:ℤ)≤y by positivity)
  have h6 := mul_le_mul_of_nonneg_right hf.2.2 (show (0:ℤ)≤r by positivity)
  have hz : numerator L U S r y t≤50174*((qt:ℤ)*t+(qy:ℤ)*y+(qr:ℤ)*r) := by
    unfold numerator
    nlinarith only [h1,h2,h3,h4,h5,h6]
  rw [←numerator_eq L U S r y t hr] at hz
  have hn : leftRegularNumerator (pair L U S r y t)≤50174*(qt*t+qy*y+qr*r) := by exact_mod_cast hz
  have hd := Nat.div_le_div_right (c:=50174) hn
  simpa [leftRegularCountCap,pair,UnequalParameters.gap] using hd

end ProximityPrize.SubmissionLower.BalancedPhasePotential6815

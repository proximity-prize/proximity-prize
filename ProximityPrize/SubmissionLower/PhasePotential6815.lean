import ProximityPrize.SubmissionLower.LowerGeometry
namespace ProximityPrize.SubmissionLower.PhasePotential6815
open RCN260 AsymmetricHelper
set_option autoImplicit false
set_option maxHeartbeats 1000000

def pair (capT capY capR r y t : ℕ) : UnequalParameters :=
  ⟨262144,131071,181245,y,r,t,capY,capR,capT⟩

def numerator (capT capY capR r y t : ℤ) : ℤ :=
  4*131073*131071*(capT*r*y+capR*t*y+capY*t*r) +
  131073*(capR-131071*capY)*t +
  (131073*(capR-131071*capT)+80900*50174*capR)*y +
  (131073*(capT+capY)+80900*50174*capY)*r

theorem numerator_eq (capT capY capR r y t : ℕ) (hr : 1≤r) :
    (leftRegularNumerator (pair capT capY capR r y t) : ℤ)=
      numerator capT capY capR r y t := by
  have hsub : ((2*r-1 : ℕ) : ℤ)=2*(r:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*r)]
    push_cast
    ring
  simp only [leftRegularNumerator,pair,UnequalParameters.errors,UnequalParameters.gap,
    UnequalParameters.leftAgreement,UnequalParameters.mixedCost,RCN294.dot]
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [hsub]
  norm_num [numerator]
  ring

private theorem box_product (x y capX capY : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hX : x≤capX) (hY : y≤capY) :
    2*x*y≤capX*y+capY*x := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) hy,mul_nonneg (sub_nonneg.mpr hY) hx]

theorem half_middle_raw (r y t : ℤ)
    (hr : 0≤r) (hy : 0≤y) (ht : 0≤t)
    (hR : r≤39) (hY : y≤182) (hT : t≤11192) :
    numerator 531000 11062 2470 r y t ≤
      50174*(445577482556*t+42396791527856*y+150966183228926*r) := by
  have hry := box_product r y 39 182 hr hy hR hY
  have hrt := box_product r t 39 11192 hr ht hR hT
  have hty : 4*t*y≤182*t+3*11192*y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hY) ht,mul_nonneg (sub_nonneg.mpr hT) hy]
  dsimp [numerator]
  nlinarith

theorem final_pass_raw (r y t : ℤ)
    (hr : 0≤r) (hy : 0≤y) (ht : 0≤t)
    (hY : y≤182) (hT : t≤11192) :
    numerator 88902 1382 308 r y t ≤
      50174*(4690861953401*y+43345274666350*r) := by
  have hry : r*y≤182*r := by nlinarith [mul_nonneg (sub_nonneg.mpr hY) hr]
  have hty : t*y≤11192*y := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) hy]
  have htr : t*r≤11192*r := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) hr]
  dsimp [numerator]
  nlinarith

theorem half_middle_count (r y t : ℕ) (hr : 1≤r)
    (hR : r≤39) (hY : y≤182) (hT : t≤11192) :
    leftRegularCountCap (pair 531000 11062 2470 r y t) ≤
      445577482556*t+42396791527856*y+150966183228926*r := by
  have hz := half_middle_raw (r:ℤ) y t (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hR) (by exact_mod_cast hY) (by exact_mod_cast hT)
  have he := numerator_eq 531000 11062 2470 r y t hr
  norm_num only [Nat.cast_ofNat] at he
  rw [← he] at hz
  have hn : leftRegularNumerator (pair 531000 11062 2470 r y t) ≤
      50174*(445577482556*t+42396791527856*y+150966183228926*r) := by exact_mod_cast hz
  have hd := Nat.div_le_div_right (c:=50174) hn
  simpa [leftRegularCountCap,pair,UnequalParameters.gap] using hd

theorem final_pass_count (r y t : ℕ) (hr : 1≤r)
    (hY : y≤182) (hT : t≤11192) :
    leftRegularCountCap (pair 88902 1382 308 r y t) ≤
      4690861953401*y+43345274666350*r := by
  have hz := final_pass_raw (r:ℤ) y t (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hY) (by exact_mod_cast hT)
  have he := numerator_eq 88902 1382 308 r y t hr
  norm_num only [Nat.cast_ofNat] at he
  rw [← he] at hz
  have hn : leftRegularNumerator (pair 88902 1382 308 r y t) ≤
      50174*(4690861953401*y+43345274666350*r) := by exact_mod_cast hz
  have hd := Nat.div_le_div_right (c:=50174) hn
  simpa [leftRegularCountCap,pair,UnequalParameters.gap] using hd

theorem count_mono_right (loT loY loR hiT hiY hiR r y t : ℕ)
    (hT : loT≤hiT) (hY : loY≤hiY) (hR : loR≤hiR) :
    leftRegularCountCap (pair loT loY loR r y t) ≤
      leftRegularCountCap (pair hiT hiY hiR r y t) := by
  unfold leftRegularCountCap
  apply Nat.div_le_div_right
  simp only [leftRegularNumerator,pair,UnequalParameters.errors,UnequalParameters.gap,
    UnequalParameters.leftAgreement,UnequalParameters.mixedCost,RCN294.dot]
  gcongr

end ProximityPrize.SubmissionLower.PhasePotential6815

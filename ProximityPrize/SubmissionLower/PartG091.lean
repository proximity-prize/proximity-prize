import ProximityPrize.SubmissionLower.PartG090


section Compact_SecondJetProperReceipts
/-! Exact nonnegative slack identities put every proper-helper branch under
its normal C2 cost. No finite enumeration or native evaluation is involved. -/
namespace ProximityPrize.SubmissionLower.SecondJetProperReceipts
open SecondJetNumericGeometry RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def slack116 (r v z : ℕ) : ℕ :=
    108615778419411981276 +
    48678024703589632*z +
    45564957034536385370*v +
    20385444091940586*v*z +
    10019188187352810*v^2 +
    82226540854352201738*r +
    36815432271274244*r*z +
    22984650602796992600*r*v +
    10275300493497516*r*v*z +
    5092192312890540*r*v^2 +
    11386929192546398362*r^2 +
    5092192312890540*r^2*z +
    5001276445174104*r^2*v +
    1636786859152556*r^3

theorem exact_116 (r v z : ℕ) :
    50282*normal (r+3) (v+2) (z+2234) =
      (properParameters (r+3) (v+2) (z+2234) 47 157 2233 21).regularNumerator+
      slack116 r v z := by
  rw [regularNumerator_right _ (by dsimp [properParameters]; omega)
    (by dsimp [properParameters]; omega) (by dsimp [properParameters]; omega)]
  have h1 : r+3-1 = r+2 := by omega
  have h2 : r+3-2 = r+1 := by omega
  have h3 : v+2-1 = v+1 := by omega
  have h4 : r+3+(v+2)-1 = r+v+4 := by omega
  have h5 : r+3+(v+2)+(z+2234)-1 = r+v+z+2238 := by omega
  have h6 : 2*(47+21*(r+2))-1 = 93+42*(r+2) := by omega
  simp only [properParameters,UnequalParameters.rightAgreement,UnequalParameters.mixedCost,
    UnequalParameters.errors,UnequalParameters.gap,RCN294.dot,normal,flagMixed,h1,h2,h3,h4,h5,h6]
  norm_num [slack116]
  ring

theorem proper_le_normal_116 (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) (hz : 2233 < z) :
    (properParameters r v z 47 157 2233 21).regularCountCap ≤ normal r v z := by
  obtain ⟨r,rfl⟩ : ∃ a, r=a+3 := ⟨r-3,by omega⟩
  obtain ⟨v,rfl⟩ : ∃ a, v=a+2 := ⟨v-2,by omega⟩
  obtain ⟨z,rfl⟩ : ∃ a, z=a+2234 := ⟨z-2234,by omega⟩
  have h := exact_116 r v z
  have hnum : (properParameters (r+3) (v+2) (z+2234) 47 157 2233 21).regularNumerator ≤
      50282*normal (r+3) (v+2) (z+2234) := by omega
  unfold UnequalParameters.regularCountCap
  rw [show (properParameters (r+3) (v+2) (z+2234) 47 157 2233 21).gap = 50282 by norm_num [properParameters,UnequalParameters.gap]]
  have hh := Nat.div_le_div_right (c := 50282) hnum
  simpa only [Nat.mul_div_right _ (by decide : 0 < 50282)] using hh

def slack96 (r v z : ℕ) : ℕ :=
    106460692166175190610 +
    49742300423408416*z +
    43953022106043697111*v +
    20505290859361194*v*z +
    10139034954773418*v^2 +
    79726629106466024406*r +
    37220464868181236*r*z +
    22108548104538179104*r*v +
    10306636574887308*r*v*z +
    5123528394280332*r*v^2 +
    10987552800136006050*r^2 +
    5123528394280332*r^2*z +
    5063948607953688*r^2*v +
    1668122940542348*r^3

theorem exact_96 (r v z : ℕ) :
    50282*normal (r+3) (v+2) (z+2142) =
      (properParameters (r+3) (v+2) (z+2142) 38 130 2141 17).regularNumerator+
      slack96 r v z := by
  rw [regularNumerator_right _ (by dsimp [properParameters]; omega)
    (by dsimp [properParameters]; omega) (by dsimp [properParameters]; omega)]
  have h1 : r+3-1 = r+2 := by omega
  have h2 : r+3-2 = r+1 := by omega
  have h3 : v+2-1 = v+1 := by omega
  have h4 : r+3+(v+2)-1 = r+v+4 := by omega
  have h5 : r+3+(v+2)+(z+2142)-1 = r+v+z+2146 := by omega
  have h6 : 2*(38+17*(r+2))-1 = 75+34*(r+2) := by omega
  simp only [properParameters,UnequalParameters.rightAgreement,UnequalParameters.mixedCost,
    UnequalParameters.errors,UnequalParameters.gap,RCN294.dot,normal,flagMixed,h1,h2,h3,h4,h5,h6]
  norm_num [slack96]
  ring

theorem proper_le_normal_96 (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) (hz : 2141 < z) :
    (properParameters r v z 38 130 2141 17).regularCountCap ≤ normal r v z := by
  obtain ⟨r,rfl⟩ : ∃ a, r=a+3 := ⟨r-3,by omega⟩
  obtain ⟨v,rfl⟩ : ∃ a, v=a+2 := ⟨v-2,by omega⟩
  obtain ⟨z,rfl⟩ : ∃ a, z=a+2142 := ⟨z-2142,by omega⟩
  have h := exact_96 r v z
  have hnum : (properParameters (r+3) (v+2) (z+2142) 38 130 2141 17).regularNumerator ≤
      50282*normal (r+3) (v+2) (z+2142) := by omega
  unfold UnequalParameters.regularCountCap
  rw [show (properParameters (r+3) (v+2) (z+2142) 38 130 2141 17).gap = 50282 by norm_num [properParameters,UnequalParameters.gap]]
  have hh := Nat.div_le_div_right (c := 50282) hnum
  simpa only [Nat.mul_div_right _ (by decide : 0 < 50282)] using hh

def slack108 (r v z : ℕ) : ℕ :=
    103905576192488885256 +
    49246523756821453*z +
    43223895133305162495*v +
    20452445581754286*v*z +
    10086189677166510*v^2 +
    78191512289925204604*r +
    37025782590075188*r*z +
    21767177693130985176*r*v +
    10291793167913196*r*v*z +
    5108684987306220*r*v^2 +
    10801728479424628310*r^2 +
    5108684987306220*r^2*z +
    5034261794005464*r^2*v +
    1653279533568236*r^3

theorem exact_108 (r v z : ℕ) :
    50282*normal (r+3) (v+2) (z+2112) =
      (properParameters (r+3) (v+2) (z+2112) 41 146 2111 19).regularNumerator+
      slack108 r v z := by
  rw [regularNumerator_right _ (by dsimp [properParameters]; omega)
    (by dsimp [properParameters]; omega) (by dsimp [properParameters]; omega)]
  have h1 : r+3-1 = r+2 := by omega
  have h2 : r+3-2 = r+1 := by omega
  have h3 : v+2-1 = v+1 := by omega
  have h4 : r+3+(v+2)-1 = r+v+4 := by omega
  have h5 : r+3+(v+2)+(z+2112)-1 = r+v+z+2116 := by omega
  have h6 : 2*(41+19*(r+2))-1 = 81+38*(r+2) := by omega
  simp only [properParameters,UnequalParameters.rightAgreement,UnequalParameters.mixedCost,
    UnequalParameters.errors,UnequalParameters.gap,RCN294.dot,normal,flagMixed,h1,h2,h3,h4,h5,h6]
  norm_num [slack108]
  ring

theorem proper_le_normal_108 (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) (hz : 2111 < z) :
    (properParameters r v z 41 146 2111 19).regularCountCap ≤ normal r v z := by
  obtain ⟨r,rfl⟩ : ∃ a, r=a+3 := ⟨r-3,by omega⟩
  obtain ⟨v,rfl⟩ : ∃ a, v=a+2 := ⟨v-2,by omega⟩
  obtain ⟨z,rfl⟩ : ∃ a, z=a+2112 := ⟨z-2112,by omega⟩
  have h := exact_108 r v z
  have hnum : (properParameters (r+3) (v+2) (z+2112) 41 146 2111 19).regularNumerator ≤
      50282*normal (r+3) (v+2) (z+2112) := by omega
  unfold UnequalParameters.regularCountCap
  rw [show (properParameters (r+3) (v+2) (z+2112) 41 146 2111 19).gap = 50282 by norm_num [properParameters,UnequalParameters.gap]]
  have hh := Nat.div_le_div_right (c := 50282) hnum
  simpa only [Nat.mul_div_right _ (by decide : 0 < 50282)] using hh

end ProximityPrize.SubmissionLower.SecondJetProperReceipts

end Compact_SecondJetProperReceipts

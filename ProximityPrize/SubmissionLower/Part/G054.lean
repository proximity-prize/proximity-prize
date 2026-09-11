import ProximityPrize.SubmissionLower.Part.G053


section Compact_SecondJetPoleScaling
/-! A nonzero constant factor in the second derivative does not change poles. -/
namespace ProximityPrize.SubmissionLower.SecondJetPoleScaling
open RCN026 RCN187
noncomputable section
set_option autoImplicit false
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem pole_div_constant (v : Place K E) (a : K) (ha : a ≠ 0) (x : E) :
    poleOrder v.val (x/algebraMap K E a) = poleOrder v.val x := by
  letI : v.val.IsTrivialOn K := v.property.2
  have hc : v.val (algebraMap K E a) = 1 := Valuation.IsTrivialOn.eq_one a ha
  simp only [poleOrder,Valuation.map_div,hc,div_one]

theorem pole_half (v : Place K E) (h2 : (2 : K) ≠ 0) (x : E) :
    poleOrder v.val (x/2) = poleOrder v.val x := by
  simpa only [map_ofNat] using pole_div_constant v 2 h2 x

end
end ProximityPrize.SubmissionLower.SecondJetPoleScaling

end Compact_SecondJetPoleScaling

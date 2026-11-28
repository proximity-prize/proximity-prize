import ProximityPrize.SubmissionLower.Bundle6970_e9c9ffc1f3ae0072
import ProximityPrize.SubmissionLower.Z6970H2307GateNumeric
import ProximityPrize.SubmissionLower.Z6970H2307PreciseOrdinary
import ProximityPrize.SubmissionLower.Bundle6970_d75c3b3cfe512e92
import ProximityPrize.SubmissionLower.Bundle6970_b1fddbff8e4dffbb

section Pack_Z6970H2307GateData084Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data084

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true) (ht : tfB (shape f) = true)
    (hth : thOK (rayT (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hmatrix : ∀ i k, (tpOf (hiS G) 133446 (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133446
    (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data084
end Pack_Z6970H2307GateData084Price

section Pack_Z6970H2307GateData085Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data085

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true) (ht : tfB (shape f) = true)
    (hth : thOK (rayT (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hmatrix : ∀ i k, (tpOf (hiS G) 133446 (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133446
    (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data085
end Pack_Z6970H2307GateData085Price

section Pack_Z6970H2307GateData086Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data086

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true) (ht : tfB (shape f) = true)
    (hth : thOK (rayT (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hmatrix : ∀ i k, (tpOf (hiS G) 133446 (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133446
    (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data086
end Pack_Z6970H2307GateData086Price

section Pack_Z6970H2307GateData087Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data087

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true) (ht : tfB (shape f) = true)
    (hth : thOK (rayT (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hmatrix : ∀ i k, (tpOf (hiS G) 133446 (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133446
    (Low6969Prices.bentLift 133446 (hiS G)).2 (Low6969Prices.bentLift 133447 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data087
end Pack_Z6970H2307GateData087Price

section Pack_Z6970H2307GateData088Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data088

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true)
    (hth : thOK (rayO (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
  have hmatrix : ∀ i k, (opOf (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)).ray i k = Gt.mat G i k := by decide +kernel
  have h := price_O_precise hm hceil hf hon hl cut chars hcx G ok rfl rfl
    (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩
    (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)
    hmatrix
    (numO G (shape f)) DEN (Ax (numO G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayO, numO] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = true from rfl] using h

end ExpandedGate6970.H2307Data088
end Pack_Z6970H2307GateData088Price

section Pack_Z6970H2307GateData089Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data089

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true)
    (hth : thOK (rayO (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
  have hmatrix : ∀ i k, (opOf (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)).ray i k = Gt.mat G i k := by decide +kernel
  have h := price_O_precise hm hceil hf hon hl cut chars hcx G ok rfl rfl
    (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩
    (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)
    hmatrix
    (numO G (shape f)) DEN (Ax (numO G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayO, numO] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = true from rfl] using h

end ExpandedGate6970.H2307Data089
end Pack_Z6970H2307GateData089Price

section Pack_Z6970H2307GateData090Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data090

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true)
    (hth : thOK (rayO (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
  have hmatrix : ∀ i k, (opOf (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)).ray i k = Gt.mat G i k := by decide +kernel
  have h := price_O_precise hm hceil hf hon hl cut chars hcx G ok rfl rfl
    (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩
    (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)
    hmatrix
    (numO G (shape f)) DEN (Ax (numO G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayO, numO] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = true from rfl] using h

end ExpandedGate6970.H2307Data090
end Pack_Z6970H2307GateData090Price

section Pack_Z6970H2307GateData091Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data091

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true)
    (hth : thOK (rayO (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
  have hmatrix : ∀ i k, (opOf (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)).ray i k = Gt.mat G i k := by decide +kernel
  have h := price_O_precise hm hceil hf hon hl cut chars hcx G ok rfl rfl
    (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩
    (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)
    hmatrix
    (numO G (shape f)) DEN (Ax (numO G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayO, numO] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = true from rfl] using h

end ExpandedGate6970.H2307Data091
end Pack_Z6970H2307GateData091Price

section Pack_Z6970H2307GateData092Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data092

open P3 (K)
open K1_13 (Row shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)
open ExpandedGate6970.Numeric
open scoped Polynomial

theorem price {w : P3.I → K} {Γ : Finset K} {s : K → Polynomial K} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank)
    (hf : Low6969Prices.SmallFactor f) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (hl : 0 < l) (cut : Low6969Prices.ProperCut f Γ s l) (chars : f.degreeOf 3 < K1.p)
    (hin : inR G (shape f) = true)
    (hth : thOK (rayO (shape f)) (Gt.mat G) = true) :
    Γ.card ≤ quote G (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedThirdCut.preciseFee (shape f) l := by
  obtain ⟨b0,b1,b2,u0,u1,u2⟩ := inR_props hin
  have hθ := thOK_spec hth
  have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
  have hmatrix : ∀ i k, (opOf (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)).ray i k = Gt.mat G i k := by decide +kernel
  have h := price_O_precise hm hceil hf hon hl cut chars hcx G ok rfl rfl
    (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩
    (K1_13.chart 133451 (hiS G).chamber) (K1_13.chart 133452 (hiS G).chamber)
    hmatrix
    (numO G (shape f)) DEN (Ax (numO G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayO, numO] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = true from rfl] using h

end ExpandedGate6970.H2307Data092
end Pack_Z6970H2307GateData092Price

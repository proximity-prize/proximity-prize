import ProximityPrize.SubmissionLower.Bundle6970_b32d8c9aa1ff9554
import ProximityPrize.SubmissionLower.Z6970H2307GateNumeric
import ProximityPrize.SubmissionLower.Z6970H2307PreciseOrdinary
import ProximityPrize.SubmissionLower.Bundle6970_e9c9ffc1f3ae0072
import ProximityPrize.SubmissionLower.Bundle6970_b1fddbff8e4dffbb
import ProximityPrize.SubmissionLower.Bundle6970_4ccb490ce07f2bd0

section Pack_Z6970H2307GateData000Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data000

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

end ExpandedGate6970.H2307Data000
end Pack_Z6970H2307GateData000Price

section Pack_Z6970H2307GateData001Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data001

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

end ExpandedGate6970.H2307Data001
end Pack_Z6970H2307GateData001Price

section Pack_Z6970H2307GateData002Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data002

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

end ExpandedGate6970.H2307Data002
end Pack_Z6970H2307GateData002Price

section Pack_Z6970H2307GateData003Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data003

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

end ExpandedGate6970.H2307Data003
end Pack_Z6970H2307GateData003Price

section Pack_Z6970H2307GateData004Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data004

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

end ExpandedGate6970.H2307Data004
end Pack_Z6970H2307GateData004Price

section Pack_Z6970H2307GateData005Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data005

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

end ExpandedGate6970.H2307Data005
end Pack_Z6970H2307GateData005Price

section Pack_Z6970H2307GateData006Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data006

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

end ExpandedGate6970.H2307Data006
end Pack_Z6970H2307GateData006Price

section Pack_Z6970H2307GateData007Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data007

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

end ExpandedGate6970.H2307Data007
end Pack_Z6970H2307GateData007Price

section Pack_Z6970H2307GateData008Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data008

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

end ExpandedGate6970.H2307Data008
end Pack_Z6970H2307GateData008Price

section Pack_Z6970H2307GateData009Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data009

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

end ExpandedGate6970.H2307Data009
end Pack_Z6970H2307GateData009Price

section Pack_Z6970H2307GateData010Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data010

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

end ExpandedGate6970.H2307Data010
end Pack_Z6970H2307GateData010Price

section Pack_Z6970H2307GateData011Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data011

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

end ExpandedGate6970.H2307Data011
end Pack_Z6970H2307GateData011Price

section Pack_Z6970H2307GateData012Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data012

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

end ExpandedGate6970.H2307Data012
end Pack_Z6970H2307GateData012Price

section Pack_Z6970H2307GateData013Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data013

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

end ExpandedGate6970.H2307Data013
end Pack_Z6970H2307GateData013Price

section Pack_Z6970H2307GateData014Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data014

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

end ExpandedGate6970.H2307Data014
end Pack_Z6970H2307GateData014Price

section Pack_Z6970H2307GateData015Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data015

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

end ExpandedGate6970.H2307Data015
end Pack_Z6970H2307GateData015Price

section Pack_Z6970H2307GateData016Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data016

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

end ExpandedGate6970.H2307Data016
end Pack_Z6970H2307GateData016Price

section Pack_Z6970H2307GateData017Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data017

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

end ExpandedGate6970.H2307Data017
end Pack_Z6970H2307GateData017Price

section Pack_Z6970H2307GateData018Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data018

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

end ExpandedGate6970.H2307Data018
end Pack_Z6970H2307GateData018Price

section Pack_Z6970H2307GateData019Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data019

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

end ExpandedGate6970.H2307Data019
end Pack_Z6970H2307GateData019Price

section Pack_Z6970H2307GateData020Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data020

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

end ExpandedGate6970.H2307Data020
end Pack_Z6970H2307GateData020Price

section Pack_Z6970H2307GateData021Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data021

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

end ExpandedGate6970.H2307Data021
end Pack_Z6970H2307GateData021Price

section Pack_Z6970H2307GateData022Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data022

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

end ExpandedGate6970.H2307Data022
end Pack_Z6970H2307GateData022Price

section Pack_Z6970H2307GateData023Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data023

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

end ExpandedGate6970.H2307Data023
end Pack_Z6970H2307GateData023Price

section Pack_Z6970H2307GateData024Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data024

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

end ExpandedGate6970.H2307Data024
end Pack_Z6970H2307GateData024Price

section Pack_Z6970H2307GateData025Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data025

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

end ExpandedGate6970.H2307Data025
end Pack_Z6970H2307GateData025Price

section Pack_Z6970H2307GateData026Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data026

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

end ExpandedGate6970.H2307Data026
end Pack_Z6970H2307GateData026Price

section Pack_Z6970H2307GateData027Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data027

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

end ExpandedGate6970.H2307Data027
end Pack_Z6970H2307GateData027Price

section Pack_Z6970H2307GateData028Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data028

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

end ExpandedGate6970.H2307Data028
end Pack_Z6970H2307GateData028Price

section Pack_Z6970H2307GateData029Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data029

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

end ExpandedGate6970.H2307Data029
end Pack_Z6970H2307GateData029Price

section Pack_Z6970H2307GateData030Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data030

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

end ExpandedGate6970.H2307Data030
end Pack_Z6970H2307GateData030Price

section Pack_Z6970H2307GateData031Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data031

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

end ExpandedGate6970.H2307Data031
end Pack_Z6970H2307GateData031Price

section Pack_Z6970H2307GateData032Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data032

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

end ExpandedGate6970.H2307Data032
end Pack_Z6970H2307GateData032Price

section Pack_Z6970H2307GateData033Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data033

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

end ExpandedGate6970.H2307Data033
end Pack_Z6970H2307GateData033Price

section Pack_Z6970H2307GateData034Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data034

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

end ExpandedGate6970.H2307Data034
end Pack_Z6970H2307GateData034Price

section Pack_Z6970H2307GateData035Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data035

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

end ExpandedGate6970.H2307Data035
end Pack_Z6970H2307GateData035Price

section Pack_Z6970H2307GateData036Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data036

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

end ExpandedGate6970.H2307Data036
end Pack_Z6970H2307GateData036Price

section Pack_Z6970H2307GateData037Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data037

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

end ExpandedGate6970.H2307Data037
end Pack_Z6970H2307GateData037Price

section Pack_Z6970H2307GateData038Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data038

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

end ExpandedGate6970.H2307Data038
end Pack_Z6970H2307GateData038Price

section Pack_Z6970H2307GateData039Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data039

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

end ExpandedGate6970.H2307Data039
end Pack_Z6970H2307GateData039Price

section Pack_Z6970H2307GateData040Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data040

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

end ExpandedGate6970.H2307Data040
end Pack_Z6970H2307GateData040Price

section Pack_Z6970H2307GateData041Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data041

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

end ExpandedGate6970.H2307Data041
end Pack_Z6970H2307GateData041Price

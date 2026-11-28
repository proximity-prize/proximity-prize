import ProximityPrize.SubmissionLower.Bundle6970_4ccb490ce07f2bd0
import ProximityPrize.SubmissionLower.Z6970H2307GateNumeric
import ProximityPrize.SubmissionLower.Z6970H2307PreciseOrdinary
import ProximityPrize.SubmissionLower.Bundle6970_e9c9ffc1f3ae0072
import ProximityPrize.SubmissionLower.Bundle6970_b1fddbff8e4dffbb
import ProximityPrize.SubmissionLower.Bundle6970_c1fe700b8ac80c27
import ProximityPrize.SubmissionLower.Bundle6970_d75c3b3cfe512e92

section Pack_Z6970H2307GateData042Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data042

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

end ExpandedGate6970.H2307Data042
end Pack_Z6970H2307GateData042Price

section Pack_Z6970H2307GateData043Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data043

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

end ExpandedGate6970.H2307Data043
end Pack_Z6970H2307GateData043Price

section Pack_Z6970H2307GateData044Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data044

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

end ExpandedGate6970.H2307Data044
end Pack_Z6970H2307GateData044Price

section Pack_Z6970H2307GateData045Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data045

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

end ExpandedGate6970.H2307Data045
end Pack_Z6970H2307GateData045Price

section Pack_Z6970H2307GateData046Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data046

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

end ExpandedGate6970.H2307Data046
end Pack_Z6970H2307GateData046Price

section Pack_Z6970H2307GateData047Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data047

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

end ExpandedGate6970.H2307Data047
end Pack_Z6970H2307GateData047Price

section Pack_Z6970H2307GateData048Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data048

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

end ExpandedGate6970.H2307Data048
end Pack_Z6970H2307GateData048Price

section Pack_Z6970H2307GateData049Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data049

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

end ExpandedGate6970.H2307Data049
end Pack_Z6970H2307GateData049Price

section Pack_Z6970H2307GateData050Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data050

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

end ExpandedGate6970.H2307Data050
end Pack_Z6970H2307GateData050Price

section Pack_Z6970H2307GateData051Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data051

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

end ExpandedGate6970.H2307Data051
end Pack_Z6970H2307GateData051Price

section Pack_Z6970H2307GateData052Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data052

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

end ExpandedGate6970.H2307Data052
end Pack_Z6970H2307GateData052Price

section Pack_Z6970H2307GateData053Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data053

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

end ExpandedGate6970.H2307Data053
end Pack_Z6970H2307GateData053Price

section Pack_Z6970H2307GateData054Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data054

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

end ExpandedGate6970.H2307Data054
end Pack_Z6970H2307GateData054Price

section Pack_Z6970H2307GateData055Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data055

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

end ExpandedGate6970.H2307Data055
end Pack_Z6970H2307GateData055Price

section Pack_Z6970H2307GateData056Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data056

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
  have hmatrix : ∀ i k, (opOf (K1_13.chart 133371 (hiS G).chamber) (K1_13.chart 133372 (hiS G).chamber)).ray i k = Gt.mat G i k := by decide +kernel
  have h := price_O_precise hm hceil hf hon hl cut chars hcx G ok rfl rfl
    (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩
    (K1_13.chart 133371 (hiS G).chamber) (K1_13.chart 133372 (hiS G).chamber)
    hmatrix
    (numO G (shape f)) DEN (Ax (numO G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayO, numO] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = true from rfl] using h

end ExpandedGate6970.H2307Data056
end Pack_Z6970H2307GateData056Price

section Pack_Z6970H2307GateData057Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data057

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

end ExpandedGate6970.H2307Data057
end Pack_Z6970H2307GateData057Price

section Pack_Z6970H2307GateData058Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data058

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

end ExpandedGate6970.H2307Data058
end Pack_Z6970H2307GateData058Price

section Pack_Z6970H2307GateData059Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data059

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

end ExpandedGate6970.H2307Data059
end Pack_Z6970H2307GateData059Price

section Pack_Z6970H2307GateData060Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data060

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

end ExpandedGate6970.H2307Data060
end Pack_Z6970H2307GateData060Price

section Pack_Z6970H2307GateData061Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data061

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

end ExpandedGate6970.H2307Data061
end Pack_Z6970H2307GateData061Price

section Pack_Z6970H2307GateData062Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data062

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

end ExpandedGate6970.H2307Data062
end Pack_Z6970H2307GateData062Price

section Pack_Z6970H2307GateData063Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data063

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

end ExpandedGate6970.H2307Data063
end Pack_Z6970H2307GateData063Price

section Pack_Z6970H2307GateData064Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data064

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

end ExpandedGate6970.H2307Data064
end Pack_Z6970H2307GateData064Price

section Pack_Z6970H2307GateData065Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data065

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

end ExpandedGate6970.H2307Data065
end Pack_Z6970H2307GateData065Price

section Pack_Z6970H2307GateData066Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data066

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133366 (Low6969Prices.bentLift 133366 (hiS G)).2 (Low6969Prices.bentLift 133367 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133366
    (Low6969Prices.bentLift 133366 (hiS G)).2 (Low6969Prices.bentLift 133367 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data066
end Pack_Z6970H2307GateData066Price

section Pack_Z6970H2307GateData067Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data067

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data067
end Pack_Z6970H2307GateData067Price

section Pack_Z6970H2307GateData068Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data068

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data068
end Pack_Z6970H2307GateData068Price

section Pack_Z6970H2307GateData069Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data069

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data069
end Pack_Z6970H2307GateData069Price

section Pack_Z6970H2307GateData070Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data070

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data070
end Pack_Z6970H2307GateData070Price

section Pack_Z6970H2307GateData071Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data071

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data071
end Pack_Z6970H2307GateData071Price

section Pack_Z6970H2307GateData072Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data072

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data072
end Pack_Z6970H2307GateData072Price

section Pack_Z6970H2307GateData073Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data073

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data073
end Pack_Z6970H2307GateData073Price

section Pack_Z6970H2307GateData074Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data074

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data074
end Pack_Z6970H2307GateData074Price

section Pack_Z6970H2307GateData075Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data075

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data075
end Pack_Z6970H2307GateData075Price

section Pack_Z6970H2307GateData076Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data076

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data076
end Pack_Z6970H2307GateData076Price

section Pack_Z6970H2307GateData077Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data077

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data077
end Pack_Z6970H2307GateData077Price

section Pack_Z6970H2307GateData078Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data078

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data078
end Pack_Z6970H2307GateData078Price

section Pack_Z6970H2307GateData079Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data079

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data079
end Pack_Z6970H2307GateData079Price

section Pack_Z6970H2307GateData080Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data080

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data080
end Pack_Z6970H2307GateData080Price

section Pack_Z6970H2307GateData081Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data081

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data081
end Pack_Z6970H2307GateData081Price

section Pack_Z6970H2307GateData082Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data082

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data082
end Pack_Z6970H2307GateData082Price

section Pack_Z6970H2307GateData083Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace ExpandedGate6970.H2307Data083

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
  have hmatrix : ∀ i k, (tpOf (hiS G) 133375 (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2).ray i k = Gt.mat G i k := by decide +kernel
  simp only [hiS] at hmatrix
  have h := price_T_precise hm hceil hf hon hl cut chars (tfB_true ht) G ok rfl rfl
    (by decide) (by decide) (by decide) (by decide) ⟨b0,b1,b2⟩ ⟨u0,u1,u2⟩ kT 133375
    (Low6969Prices.bentLift 133375 (hiS G)).2 (Low6969Prices.bentLift 133376 (hiS G)).2
    (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT+1) (shape f)).2
    rfl rfl rfl rfl rfl hmatrix
    (numT G (shape f)) DEN (Ax (numT G (shape f)) G.A)
    (by decide) (by simpa only [hmatrix, rayT, numT, hiS] using hθ) (ceil_le _ _ (by decide))
    1 ws certTable lv n length (by decide +kernel) (by decide) finite_check rho amax
    (by decide) (by decide) bounded tail0 tail1 tail2 (hsum_of lv n length (by decide) hsum)
  simpa [quote, show G.lift = false from rfl] using h

end ExpandedGate6970.H2307Data083
end Pack_Z6970H2307GateData083Price

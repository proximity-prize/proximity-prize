import ProximityPrize.SubmissionLower.Rect51Fee

/-! One-cut tariff derived from the public kaankolcu 69.50 note
f9161583-1b70-4048-8a65-bae6ee236fe4. -/
namespace Rect51Proper

def kappa (hi v₀ v₁ : ℕ) : ℕ :=
  max 1 (max (P1_7.ceilRatio (2*hi) (max 1 v₀)) (P1_7.ceilRatio (2*hi) (max 1 v₁)))

def properFee (A lo hi e v₀ v₁ : ℕ) : ℕ :=
  let L := 131071-lo
  let d := 131071+hi
  let gap := A-d
  let k := kappa hi v₀ v₁
  let G := Rect51Fee.graphDegree e v₀ v₁ (max 1 v₀) (max 1 v₁)
  P1_7.ceilRatio (G*(L+1+k)*(262144*gap*L+A*(262144-d)*k)) (A*gap)

end Rect51Proper

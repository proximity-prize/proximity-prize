import ProximityPrize.SubmissionLower.HighBanks82180


namespace HighPrices82180

open P3 (HighBand)
open P3_7 (Grade grades degreeAt quotientOrder ceilRatio singularFee)
open HighBanks82180 (start)

/-- The retained-root fee with a variable agreement threshold. -/
def price (A lo hi e v : ℕ) : ℕ := Id.run do
  if v = 0 then return e
  let gap := A - degreeAt hi
  let scale := A * gap
  let mu := A * (262144 - degreeAt hi)
  let bn := 262144 * gap * quotientOrder lo
  if e ≤ 2 then
    let a := mu + 2*bn*(e-1)
    let b := 2*hi*mu + 2*bn*v
    return singularFee e v + (ceilRatio (e*b^2 + 2*v*a*b) (scale^2) + e)
  let bc := quotientOrder lo + 1
  let ac := 1 + bc*(e-1)
  let cc := bc*v + 2*hi
  let an := mu + bn*(e-1)
  let cn := bn*v + 2*hi*mu
  let proper := ceilRatio (e*cc*cn +
    v*(cn*((2*e-2)*bc + ac) + cc*((2*e-2)*bn + an)) +
    v^2*((ac-2*bc)*bn + an*bc)) scale
  return singularFee e v + (proper + ceilRatio ((262144-A)*(P3.p+1)*v) gap + e)

def finish : HighBand → ℕ
  | .h2274 => 2342
  | .h2294 => 7772
  | .h7773 => 33287

def cap : HighBand → ℕ
  | .h2274 => 181608144002488886
  | .h2294 => 147576176549741790
  | .h7773 => 294196720412100

end HighPrices82180

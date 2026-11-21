import ProximityPrize.SubmissionLower.HighBanks82170

set_option Elab.async false

namespace HighPrices82170

open P3 (HighBand)
open P3_7 (Grade grades degreeAt quotientOrder ceilRatio singularFee)
open HighBanks82170 (start)

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

theorem old_price (lo hi e v : ℕ) : price 179983 lo hi e v = P3_7.wholePrice lo hi e v := by
  by_cases hv : v = 0 <;> by_cases he : e ≤ 2 <;>
    simp [price, P3_7.wholePrice, hv, he, P3_7.tangentFee, P3_7.properFee, P3_7.flatFee,
      P3_7.persistentFee, P3_7.scale, P3_7.gap, P3_7.lambdaNum, P3_7.muNum]
  all_goals rfl

def finish : HighBand → ℕ
  | .h2274 => 2317
  | .h2294 => 7772
  | .h7773 => 33267

def cap : HighBand → ℕ
  | .h2274 => 181671044293514813
  | .h2294 => 147625264377006431
  | .h7773 => 294115765647887

private def maxPrice (lo hi e : ℕ) : List Grade → ℕ
  | [] => 0
  | g :: gs => max (price 179974 lo hi e g.seedCap) (maxPrice lo hi (e+1) gs)

private theorem get_le (lo hi e : ℕ) (gs : List Grade) (i : Fin gs.length) :
    price 179974 lo hi (i.val+e) (gs.get i).seedCap ≤ maxPrice lo hi e gs := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · simp [maxPrice]
    · have h := ih (e+1) ⟨j, by simpa using hj⟩
      change price 179974 lo hi (j+1+e) (gs.get ⟨j, _⟩).seedCap ≤ _
      rw [show j+1+e = j+(e+1) by omega]
      exact h.trans (Nat.le_max_right _ _)

theorem exact_max (b : HighBand) : maxPrice (start b) (finish b) 1 (grades b) = cap b := by
  cases b <;> decide +kernel

theorem retained_fee (b : HighBand) (i : P3_7.GradeIndex b) :
    price 179974 (start b) (finish b) (i.val+1) ((grades b).get i).seedCap ≤ cap b :=
  (get_le _ _ _ _ i).trans_eq (exact_max b)

#print axioms retained_fee

end HighPrices82170

import ProximityPrize.SubmissionLower.Z6970H2307GateAmbientFast

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Leading

def den (x : ℤ) : ℤ := if x < 0 then 0 else (Gate6966Cell.denN x.toNat : ℤ)

def StepRule (P : ℕ → ℤ → ℤ) : Prop :=
  ∀ (a : ℕ) (x : ℤ), 1 ≤ a → a ≤ 3 → x ≤ 1679 → P a x - P a (x - a) = den x

end Gate6970Leading

import ProximityPrize.SubmissionLower.BoundaryTailCounting

/-! Per-cell pair charge. The residual pair `(Q, T) = (QB/H, QA/H)` only has the
complement of the universal flag `(r, y, t)` of `H` left in the `B` and `TCap`
boxes, and its count needs only the carrier's (left) agreement caps. The
numerator is affine in `t`; `line` is the integer affine majorant that the
ledger runs check at their endpoints. -/
namespace ProximityPrize.SubmissionLower.PairCell6813
open RCN260 RCN294 AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Left box `(185-y, 40-r, 27313-t)`, right box `(312-y, 70-r, 10172-t)`. -/
def parameters (r y t : ℕ) : UnequalParameters :=
  ⟨262144,131071,181265,185-y,40-r,27313-t,312-y,70-r,10172-t⟩

def cap (r y t : ℕ) : ℕ := leftRegularCountCap (parameters r y t)

def constant (r y : ℕ) : ℕ := leftRegularNumerator (parameters r y 0)

def slope (r y : ℕ) : ℕ :=
  131073*((1+2*131071*(185-y))*((40-r)+(70-r)) +
    131071*(2*(40-r)-1)*((185-y)+(312-y)) +
    2*131071*((185-y)*(70-r)+(40-r)*(312-y)))

theorem numerator_affine (r y t : ℕ) (ht : t ≤ 10172) :
    leftRegularNumerator (parameters r y t) + slope r y * t = constant r y := by
  have ht' : t ≤ 27313 := by omega
  simp only [constant, slope, parameters, leftRegularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.leftAgreement, UnequalParameters.mixedCost,
    dot, Nat.sub_zero]
  zify [ht, ht']
  ring

def line (r y t : ℕ) : ℤ :=
  ((constant r y / 50194 : ℕ) : ℤ) - ((slope r y / 50194 : ℕ) : ℤ) * (t : ℤ)

theorem cap_le_line (r y t : ℕ) (ht : t ≤ 10172) : (cap r y t : ℤ) ≤ line r y t := by
  have he := numerator_affine r y t ht
  have h1 := Nat.div_mul_le_self (leftRegularNumerator (parameters r y t)) 50194
  have h2 := Nat.div_add_mod (constant r y) 50194
  have h3 := Nat.mod_lt (constant r y) (show 0 < 50194 by norm_num)
  have h4 := Nat.mul_le_mul_right t (Nat.div_mul_le_self (slope r y) 50194)
  have hn : cap r y t + slope r y / 50194 * t ≤ constant r y / 50194 := by
    have hc : cap r y t = leftRegularNumerator (parameters r y t) / 50194 := by
      simp only [cap, leftRegularCountCap, parameters, UnequalParameters.gap]
    have h5 : slope r y / 50194 * 50194 * t = 50194 * (slope r y / 50194 * t) := by ring
    rw [h5] at h4
    rw [hc]
    generalize slope r y / 50194 * t = P at *
    generalize slope r y * t = S at *
    omega
  unfold line
  have hn' := (Nat.cast_le (α := ℤ)).mpr hn
  rw [Nat.cast_add, Nat.cast_mul] at hn'
  linarith

end ProximityPrize.SubmissionLower.PairCell6813

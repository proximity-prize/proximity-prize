import ProximityPrize.SubmissionLower.BoundaryTailCounting
namespace ProximityPrize.SubmissionLower.PairCell6815
open RCN260 RCN294 AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def parameters (r y t : ℕ) : UnequalParameters :=
  ⟨262144,131071,181245,229-y,50-r,15421-t,348-y,78-r,11193-t⟩

def cap (r y t : ℕ) : ℕ := leftRegularCountCap (parameters r y t)

def constant (r y : ℕ) : ℕ := leftRegularNumerator (parameters r y 0)

def slope (r y : ℕ) : ℕ :=
  131073*((1+2*131071*(229-y))*((50-r)+(78-r)) +
    131071*(2*(50-r)-1)*((229-y)+(348-y)) +
    2*131071*((229-y)*(78-r)+(50-r)*(348-y)))

theorem numerator_affine (r y t : ℕ) (ht : t ≤ 11193) :
    leftRegularNumerator (parameters r y t) + slope r y * t = constant r y := by
  have ht' : t ≤ 15421 := by omega
  simp only [constant, slope, parameters, leftRegularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.leftAgreement, UnequalParameters.mixedCost,
    dot, Nat.sub_zero]
  zify [ht, ht']
  ring

def line (r y t : ℕ) : ℤ :=
  ((constant r y / 50174 : ℕ) : ℤ) - ((slope r y / 50174 : ℕ) : ℤ) * (t : ℤ)

theorem cap_le_line (r y t : ℕ) (ht : t ≤ 11193) : (cap r y t : ℤ) ≤ line r y t := by
  have he := numerator_affine r y t ht
  have h1 := Nat.div_mul_le_self (leftRegularNumerator (parameters r y t)) 50174
  have h2 := Nat.div_add_mod (constant r y) 50174
  have h3 := Nat.mod_lt (constant r y) (show 0 < 50174 by norm_num)
  have h4 := Nat.mul_le_mul_right t (Nat.div_mul_le_self (slope r y) 50174)
  have hn : cap r y t + slope r y / 50174 * t ≤ constant r y / 50174 := by
    have hc : cap r y t = leftRegularNumerator (parameters r y t) / 50174 := by
      simp only [cap, leftRegularCountCap, parameters, UnequalParameters.gap]
    have h5 : slope r y / 50174 * 50174 * t = 50174 * (slope r y / 50174 * t) := by ring
    rw [h5] at h4
    rw [hc]
    generalize slope r y / 50174 * t = P at *
    generalize slope r y * t = S at *
    omega
  unfold line
  have hn' := (Nat.cast_le (α := ℤ)).mpr hn
  rw [Nat.cast_add, Nat.cast_mul] at hn'
  linarith

end ProximityPrize.SubmissionLower.PairCell6815

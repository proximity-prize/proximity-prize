import ProximityPrize.SubmissionLower.BCHKSFrobeniusLinearReceivedLift6401

/-!
# Quadratic recovery of a moving linear-factor root

After a base-field projective-line reparametrization, every syndrome moment
is affine in the line parameter.  Two consecutive equations from the
degree-one Hilbert--90 normal form recover the actual primitive root by a
two-by-two Cramer determinant.  Both numerator and denominator are therefore
ordinary quadratic polynomials in the base-field parameter (no `t^q`
degree loss).

This file proves only that exact bridge.  Turning the resulting quadratic
locator pencil into a common normalized received word is a separate lifting
step.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusQuadraticRootRecovery6401

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

def cramerRootDen
    {K : Type*} [Field K] (sigma : K →+* K) (S₀ S₁ : K) : K :=
  S₀ * sigma S₁ - sigma S₀ * S₁

def cramerRootNum
    {K : Type*} [Field K] (sigma : K →+* K)
    (S₀ S₁ S₂ : K) : K :=
  S₀ * (sigma S₂ - S₂) - (sigma S₁ - S₁) * S₁

/-- Two consecutive semilinear recurrence equations recover the moving
root without dividing. -/
theorem cramerRootDen_mul_eq_num
    {K : Type*} [Field K] (sigma : K →+* K)
    (beta S₀ S₁ S₂ : K)
    (h₀ : beta * sigma S₀ - sigma beta * S₀ = sigma S₁ - S₁)
    (h₁ : beta * sigma S₁ - sigma beta * S₁ = sigma S₂ - S₂) :
    cramerRootDen sigma S₀ S₁ * beta =
      cramerRootNum sigma S₀ S₁ S₂ := by
  dsimp [cramerRootDen, cramerRootNum]
  linear_combination S₀ * h₁ - S₁ * h₀

theorem beta_eq_cramerRootNum_div
    {K : Type*} [Field K] (sigma : K →+* K)
    (beta S₀ S₁ S₂ : K)
    (h₀ : beta * sigma S₀ - sigma beta * S₀ = sigma S₁ - S₁)
    (h₁ : beta * sigma S₁ - sigma beta * S₁ = sigma S₂ - S₂)
    (hden : cramerRootDen sigma S₀ S₁ ≠ 0) :
    beta = cramerRootNum sigma S₀ S₁ S₂ /
      cramerRootDen sigma S₀ S₁ := by
  apply (eq_div_iff hden).2
  simpa [mul_comm] using cramerRootDen_mul_eq_num sigma beta S₀ S₁ S₂ h₀ h₁

/-- One recurrence equation follows directly from two consecutive fixed
normal-form selectors. -/
theorem root_recurrence_of_fixed_normalForm
    {K : Type*} [Field K] (sigma : K →+* K)
    (beta F₀ F₁ F₂ S₀ S₁ : K)
    (hF₀ : sigma F₀ = F₀) (hF₁ : sigma F₁ = F₁)
    (hF₂ : sigma F₂ = F₂)
    (hS₀ : S₀ = F₁ - beta * F₀)
    (hS₁ : S₁ = F₂ - beta * F₁) :
    beta * sigma S₀ - sigma beta * S₀ = sigma S₁ - S₁ := by
  rw [hS₀, hS₁]
  simp only [map_sub, map_mul, hF₀, hF₁, hF₂]
  ring

def quadraticDenZero
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ b₀ b₁ : K) : K :=
  a₀ * sigma a₁ - sigma a₀ * a₁

def quadraticDenOne
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ b₀ b₁ : K) : K :=
  a₀ * sigma b₁ + b₀ * sigma a₁ -
    sigma a₀ * b₁ - sigma b₀ * a₁

def quadraticDenTwo
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ b₀ b₁ : K) : K :=
  b₀ * sigma b₁ - sigma b₀ * b₁

def quadraticNumZero
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ a₂ : K) : K :=
  a₀ * (sigma a₂ - a₂) - (sigma a₁ - a₁) * a₁

def quadraticNumOne
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ a₂ b₀ b₁ b₂ : K) : K :=
  a₀ * (sigma b₂ - b₂) + b₀ * (sigma a₂ - a₂) -
    (sigma a₁ - a₁) * b₁ - (sigma b₁ - b₁) * a₁

def quadraticNumTwo
    {K : Type*} [Field K] (sigma : K →+* K)
    (b₀ b₁ b₂ : K) : K :=
  b₀ * (sigma b₂ - b₂) - (sigma b₁ - b₁) * b₁

/-- Along a parameter fixed by `sigma`, the Cramer denominator has ordinary
degree at most two. -/
theorem cramerRootDen_affine_expansion
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ b₀ b₁ t : K) (ht : sigma t = t) :
    cramerRootDen sigma (a₀ + t * b₀) (a₁ + t * b₁) =
      quadraticDenZero sigma a₀ a₁ b₀ b₁ +
        t * quadraticDenOne sigma a₀ a₁ b₀ b₁ +
        t ^ 2 * quadraticDenTwo sigma a₀ a₁ b₀ b₁ := by
  simp only [cramerRootDen, quadraticDenZero, quadraticDenOne,
    quadraticDenTwo, map_add, map_mul, ht]
  ring

/-- Along a parameter fixed by `sigma`, the Cramer numerator also has
ordinary degree at most two. -/
theorem cramerRootNum_affine_expansion
    {K : Type*} [Field K] (sigma : K →+* K)
    (a₀ a₁ a₂ b₀ b₁ b₂ t : K) (ht : sigma t = t) :
    cramerRootNum sigma (a₀ + t * b₀) (a₁ + t * b₁)
        (a₂ + t * b₂) =
      quadraticNumZero sigma a₀ a₁ a₂ +
        t * quadraticNumOne sigma a₀ a₁ a₂ b₀ b₁ b₂ +
        t ^ 2 * quadraticNumTwo sigma b₀ b₁ b₂ := by
  simp only [cramerRootNum, quadraticNumZero, quadraticNumOne,
    quadraticNumTwo, map_add, map_mul, ht]
  ring

/-! ## Nonmonic scaling audit

Scaling a Möbius-reparametrized received line by its denominator changes
the monic locator `X-beta` into `d·(X-beta)`.  The scaled syndromes are
affine, but the monic Cramer formula above no longer applies directly.  The
correct cleared numerator and denominator acquire one extra affine factor,
and therefore have ordinary degree at most three rather than two.
-/

def scaledCramerRootDen
    {K : Type*} [Field K] (sigma : K →+* K)
    (d S₀ S₁ : K) : K :=
  d * (S₀ * sigma S₁ - sigma S₀ * S₁)

def scaledCramerRootNum
    {K : Type*} [Field K] (sigma : K →+* K)
    (d S₀ S₁ S₂ : K) : K :=
  S₀ * (d * sigma S₂ - sigma d * S₂) -
    (d * sigma S₁ - sigma d * S₁) * S₁

/-- Division-free nonmonic Cramer identity.  Here
`S_j=d F_(j+1)-n F_j` and the monic root is `beta=n/d`. -/
theorem scaledCramerRootDen_mul_n_eq_d_mul_num
    {K : Type*} [Field K] (sigma : K →+* K)
    (d n F₀ F₁ F₂ F₃ S₀ S₁ S₂ : K)
    (hF₀ : sigma F₀ = F₀) (hF₁ : sigma F₁ = F₁)
    (hF₂ : sigma F₂ = F₂) (hF₃ : sigma F₃ = F₃)
    (hS₀ : S₀ = d * F₁ - n * F₀)
    (hS₁ : S₁ = d * F₂ - n * F₁)
    (hS₂ : S₂ = d * F₃ - n * F₂) :
    scaledCramerRootDen sigma d S₀ S₁ * n =
      d * scaledCramerRootNum sigma d S₀ S₁ S₂ := by
  rw [hS₀, hS₁, hS₂]
  simp only [scaledCramerRootDen, scaledCramerRootNum, map_sub, map_mul,
    hF₀, hF₁, hF₂, hF₃]
  ring

theorem nonmonic_beta_eq_scaledCramer_div
    {K : Type*} [Field K] (sigma : K →+* K)
    (d n F₀ F₁ F₂ F₃ S₀ S₁ S₂ : K)
    (hF₀ : sigma F₀ = F₀) (hF₁ : sigma F₁ = F₁)
    (hF₂ : sigma F₂ = F₂) (hF₃ : sigma F₃ = F₃)
    (hS₀ : S₀ = d * F₁ - n * F₀)
    (hS₁ : S₁ = d * F₂ - n * F₁)
    (hS₂ : S₂ = d * F₃ - n * F₂)
    (hd : d ≠ 0) (hD : scaledCramerRootDen sigma d S₀ S₁ ≠ 0) :
    n / d = scaledCramerRootNum sigma d S₀ S₁ S₂ /
      scaledCramerRootDen sigma d S₀ S₁ := by
  apply (div_eq_div_iff hd hD).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (scaledCramerRootDen_mul_n_eq_d_mul_num sigma d n F₀ F₁ F₂ F₃
      S₀ S₁ S₂ hF₀ hF₁ hF₂ hF₃ hS₀ hS₁ hS₂)

end BCHKSFrobeniusQuadraticRootRecovery6401
end ProximityPrize.SubmissionLower

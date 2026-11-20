import ProximityPrize.SubmissionLower.Koala6831MovingDerivation

namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

abbrev NormalizedCoeff (K : Type*) [Field K] := MvPolynomial (Fin 2) (RatFunc K)
abbrev NormalizedPoly (K : Type*) [Field K] := Polynomial (NormalizedCoeff K)

variable {K : Type*} [Field K]

def xPolynomial (K : Type*) [Field K] : Polynomial K →ₐ[K] NormalizedPoly K :=
  (IsScalarTower.toAlgHom K (RatFunc K) (NormalizedPoly K)).comp
    (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))

theorem xPolynomial_apply (f : Polynomial K) :
    xPolynomial K f =
      Polynomial.C (MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) f)) := by
  rfl

def normalizedAffine (f₀ f₁ : Polynomial K) : NormalizedPoly K :=
  xPolynomial K f₀ + Polynomial.X * xPolynomial K f₁

def normalizedValue (K : Type*) [Field K] : NormalizedPoly K :=
  Polynomial.C (MvPolynomial.X (0 : Fin 2))

def normalizedFirstJet (K : Type*) [Field K] : NormalizedPoly K :=
  Polynomial.C (MvPolynomial.X (1 : Fin 2))

private theorem velocity_identities
    {E : Type*} [CommRing E] {d dx a ax a1 a1x b bx b1 b1x q j y r yz rz : E}
    (hY : d * y = a * q - b) (hR : d * r = a * j + ax * q - bx - dx * y)
    (hYz : d * yz = a1 * q - b1) (hRz : d * rz = a1 * j + a1x * q - b1x - dx * yz) :
    let m := a1 * b - a * b1
    let mx := a1x * b + a1 * bx - ax * b1 - a * b1x
    (a * d^2 * a1 * y + d * a * m = (d * a)^2 * yz) ∧
      (d^2 * (a1x * a - a1 * ax) * y + a * d^2 * a1 * r +
        d * a * mx - (dx * a + d * ax) * m = (d * a)^2 * rz) := by
  dsimp
  constructor
  · linear_combination (d * a * a1) * hY - (d * a^2) * hYz
  · linear_combination (d * (a1x * a - a1 * ax) - a * a1 * dx) * hY +
      (a * d * a1) * hR - (d * a^2) * hRz + (dx * a^2) * hYz

namespace FlowData

variable (B : FlowData K)

def normalizedInvD0 : NormalizedPoly K :=
  algebraMap (RatFunc K) (NormalizedPoly K) ((algebraMap (Polynomial K) (RatFunc K) B.d0)⁻¹)

def normalizedY : NormalizedPoly K :=
  B.normalizedInvD0 *
    (normalizedAffine B.a0 B.a1 * normalizedValue K - normalizedAffine B.c0 B.c1)

def normalizedR : NormalizedPoly K :=
  B.normalizedInvD0 *
    (normalizedAffine B.a0 B.a1 * normalizedFirstJet K +
      normalizedAffine B.a0.derivative B.a1.derivative * normalizedValue K -
      normalizedAffine B.c0.derivative B.c1.derivative - xPolynomial K B.d0.derivative * B.normalizedY)

def normalizedCoordinates : Fin 4 → NormalizedPoly K :=
  ![xPolynomial K Polynomial.X, B.normalizedY, B.normalizedR, Polynomial.X]

def normalize : P4 K →ₐ[K] NormalizedPoly K := MvPolynomial.aeval B.normalizedCoordinates

theorem normalize_variable (i : Fin 4) :
    B.normalize (MvPolynomial.X i) = B.normalizedCoordinates i := MvPolynomial.aeval_X _ _

theorem normalize_liftX (f : Polynomial K) : B.normalize (liftX f) = xPolynomial K f := by
  have h :
      B.normalize.comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) =
        xPolynomial K := by
    apply Polynomial.algHom_ext
    simp [AlgHom.comp_apply, Polynomial.aeval_X, normalize_variable, normalizedCoordinates]
  exact DFunLike.congr_fun h f

theorem normalize_affine (f₀ f₁ : Polynomial K) :
    B.normalize (affine f₀ f₁) = normalizedAffine f₀ f₁ := by
  simp [affine, normalizedAffine, normalize_liftX, normalize_variable, normalizedCoordinates]

theorem normalize_denominator :
    B.normalize B.denominator = xPolynomial K B.d0 * normalizedAffine B.a0 B.a1 := by
  simp only [denominator, A, map_mul, normalize_affine, normalize_liftX]

theorem d0_mul_normalizedInvD0 (hd0 : B.d0 ≠ 0) :
    xPolynomial K B.d0 * B.normalizedInvD0 = 1 := by
  have hne : algebraMap (Polynomial K) (RatFunc K) B.d0 ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne hd0
  change
    algebraMap (RatFunc K) (NormalizedPoly K) (algebraMap (Polynomial K) (RatFunc K) B.d0) *
      algebraMap (RatFunc K) (NormalizedPoly K) (algebraMap (Polynomial K) (RatFunc K) B.d0)⁻¹ = 1
  rw [← map_mul, mul_inv_cancel₀ hne, map_one]

private theorem derivative_xPolynomial (f : Polynomial K) :
    (xPolynomial K f).derivative = 0 := by
  rw [xPolynomial_apply, Polynomial.derivative_C]

theorem derivative_normalizedAffine (f₀ f₁ : Polynomial K) :
    (normalizedAffine f₀ f₁).derivative = xPolynomial K f₁ := by
  simp [normalizedAffine, Polynomial.derivative_mul, derivative_xPolynomial]

private theorem derivative_normalizedInvD0 : B.normalizedInvD0.derivative = 0 := by
  unfold normalizedInvD0
  rw [Polynomial.algebraMap_apply, Polynomial.derivative_C]

theorem derivative_normalizedY :
    B.normalizedY.derivative = B.normalizedInvD0 *
      (xPolynomial K B.a1 * normalizedValue K - xPolynomial K B.c1) := by
  simp [normalizedY, Polynomial.derivative_mul, derivative_normalizedInvD0,
    derivative_normalizedAffine, normalizedValue]

theorem derivative_normalizedR :
    B.normalizedR.derivative = B.normalizedInvD0 *
      (xPolynomial K B.a1 * normalizedFirstJet K + xPolynomial K B.a1.derivative * normalizedValue K -
        xPolynomial K B.c1.derivative - xPolynomial K B.d0.derivative * B.normalizedY.derivative) := by
  simp only [normalizedR, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_add, derivative_normalizedInvD0, derivative_normalizedAffine,
    derivative_xPolynomial, normalizedValue, normalizedFirstJet, Polynomial.derivative_C,
    zero_mul, mul_zero, add_zero, zero_add]

private theorem normalize_minor :
    B.normalize B.minor =
      xPolynomial K B.a1 * normalizedAffine B.c0 B.c1 -
        normalizedAffine B.a0 B.a1 * xPolynomial K B.c1 := by
  simp only [minor, map_sub, map_mul, normalize_liftX, normalizedAffine]
  ring

private theorem normalize_minorX :
    B.normalize B.minorX =
      xPolynomial K B.a1.derivative * normalizedAffine B.c0 B.c1 +
        xPolynomial K B.a1 * normalizedAffine B.c0.derivative B.c1.derivative -
        normalizedAffine B.a0.derivative B.a1.derivative * xPolynomial K B.c1 -
        normalizedAffine B.a0 B.a1 * xPolynomial K B.c1.derivative := by
  simp only [minorX, map_sub, map_add, map_mul, normalize_liftX, normalizedAffine]
  ring

private theorem normalize_velocity (hd0 : B.d0 ≠ 0) :
    (B.normalize B.yCoefficient = (B.normalize B.denominator)^2 * B.normalizedY.derivative) ∧
      (B.normalize B.rCoefficient = (B.normalize B.denominator)^2 * B.normalizedR.derivative) := by
  have hinv := B.d0_mul_normalizedInvD0 hd0
  have hY :
      xPolynomial K B.d0 * B.normalizedY =
        normalizedAffine B.a0 B.a1 * normalizedValue K - normalizedAffine B.c0 B.c1 := by
    simp only [normalizedY, ← mul_assoc, hinv, one_mul]
  have hR :
      xPolynomial K B.d0 * B.normalizedR =
        normalizedAffine B.a0 B.a1 * normalizedFirstJet K +
          normalizedAffine B.a0.derivative B.a1.derivative * normalizedValue K -
          normalizedAffine B.c0.derivative B.c1.derivative -
          xPolynomial K B.d0.derivative * B.normalizedY := by
    simp only [normalizedR, ← mul_assoc, hinv, one_mul]
  have hYz :
      xPolynomial K B.d0 * B.normalizedY.derivative =
        xPolynomial K B.a1 * normalizedValue K - xPolynomial K B.c1 := by
    simp only [derivative_normalizedY, ← mul_assoc, hinv, one_mul]
  have hRz :
      xPolynomial K B.d0 * B.normalizedR.derivative =
        xPolynomial K B.a1 * normalizedFirstJet K +
          xPolynomial K B.a1.derivative * normalizedValue K - xPolynomial K B.c1.derivative -
          xPolynomial K B.d0.derivative * B.normalizedY.derivative := by
    simp only [B.derivative_normalizedR, ← mul_assoc, hinv, one_mul]
  simpa [yCoefficient, rCoefficient, denominatorX, A, AX, B.normalize_denominator,
    B.normalize_liftX, B.normalize_affine, B.normalize_variable, normalizedCoordinates,
    B.normalize_minor, B.normalize_minorX, mul_assoc] using
    (velocity_identities hY hR hYz hRz)

theorem normalize_flow (hd0 : B.d0 ≠ 0) (P : P4 K) :
    B.normalize (B.flow P) = (B.normalize B.denominator)^2 * (B.normalize P).derivative := by
  have hvel := B.normalize_velocity hd0
  have hvars (i : Fin 4) :
      B.normalize (B.flow (MvPolynomial.X i)) =
        (B.normalize B.denominator)^2 * (B.normalize (MvPolynomial.X i)).derivative := by
    fin_cases i
    · simp [flow_X, B.normalize_variable, normalizedCoordinates, derivative_xPolynomial]
    · simpa [flow_Y, B.normalize_variable, normalizedCoordinates] using hvel.1
    · simpa [flow_R, B.normalize_variable, normalizedCoordinates] using hvel.2
    · simp [flow_Z, B.normalize_variable, normalizedCoordinates]
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hC : B.flow (MvPolynomial.C c) = 0 := by
      simpa only [MvPolynomial.algebraMap_eq] using B.flow.map_algebraMap c
    simp only [hC, map_zero, normalize, MvPolynomial.aeval_C,
      Polynomial.algebraMap_apply, Polynomial.derivative_C, mul_zero]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, hP, hQ]
  | mul_X P i hP =>
    simp only [RCN347.leibniz_product, map_add, map_mul, Polynomial.derivative_mul, hP, hvars]
    ring

end FlowData

end

end ProximityPrize.SubmissionLower.Koala6831Moving

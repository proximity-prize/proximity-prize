import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6831MovingDerivation


namespace ProximityPrize.SubmissionLower.Koala6831Moving

noncomputable section

open ContactOrderBridge

variable {L : Type*} [Field L]

private def shifted (x : L) : Polynomial L →ₐ[L] P4 L :=
  Polynomial.aeval (MvPolynomial.X (0 : Fin 4) + MvPolynomial.C x)

private theorem localize_liftX (x u₀ u₁ : L) (f : Polynomial L) :
    localize L x u₀ u₁ (liftX f) = shifted x f := by
  have h : (localize L x u₀ u₁).comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) = shifted x := by
    apply Polynomial.algHom_ext
    simp [shifted, localize, localVariables]
  exact DFunLike.congr_fun h f

private theorem shifted_X_sub_C (x : L) : shifted x (Polynomial.X - Polynomial.C x) = MvPolynomial.X 0 := by
  simp [shifted, MvPolynomial.algebraMap_eq]

private def localizedError (B : FlowData L) (x u₀ u₁ : L) : P4 L :=
  localize L x u₀ u₁ B.yCoefficient -
    MvPolynomial.C u₁ * (localize L x u₀ u₁ B.denominator)^2 -
    MvPolynomial.X (0 : Fin 4) * localize L x u₀ u₁ B.rCoefficient

private def localizedFlow (B : FlowData L) (x u₀ u₁ : L) : Derivation L (P4 L) (P4 L) :=
  (localize L x u₀ u₁ B.denominator)^2 • MvPolynomial.pderiv (3 : Fin 4) +
    (localize L x u₀ u₁ B.rCoefficient) • MvPolynomial.pderiv (2 : Fin 4) +
    localizedError B x u₀ u₁ • MvPolynomial.pderiv (1 : Fin 4)

private theorem localizedFlow_apply (B : FlowData L) (x u₀ u₁ : L) (P : P4 L) :
    localizedFlow B x u₀ u₁ P =
      (localize L x u₀ u₁ B.denominator)^2 * MvPolynomial.pderiv (3 : Fin 4) P +
        localize L x u₀ u₁ B.rCoefficient * MvPolynomial.pderiv (2 : Fin 4) P +
        localizedError B x u₀ u₁ * MvPolynomial.pderiv (1 : Fin 4) P := by
  simp only [localizedFlow, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

private theorem localize_flow (B : FlowData L) (x u₀ u₁ : L) (P : P4 L) :
    localize L x u₀ u₁ (B.flow P) =
      localizedFlow B x u₀ u₁ (localize L x u₀ u₁ P) := by
  have hcoord (i : Fin 4) :
      localize L x u₀ u₁ (B.flow (MvPolynomial.X i)) =
        localizedFlow B x u₀ u₁ (localize L x u₀ u₁ (MvPolynomial.X i)) := by
    fin_cases i <;>
      simp [FlowData.flow_X, FlowData.flow_Y, FlowData.flow_R, FlowData.flow_Z,
        localizedFlow_apply, localizedError, localize, localVariables,
        MvPolynomial.pderiv_X]
    ring
  induction P using MvPolynomial.induction_on with
  | C c => simp [localize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [RCN347.leibniz_product, map_add, map_mul, hP, hcoord]

private def contactMinor (B : FlowData L) (u₀ u₁ : L) : Polynomial L :=
  B.a1 * (B.d0 * Polynomial.C u₀ + B.c0) -
    B.a0 * (B.d0 * Polynomial.C u₁ + B.c1)

private theorem localizedError_eq
    (B : FlowData L) (x u₀ u₁ u : L)
    (h₀ : B.d0.eval x * u₀ + B.c0.eval x = B.a0.eval x * u)
    (h₁ : B.d0.eval x * u₁ + B.c1.eval x = B.a1.eval x * u) :
    ∃ f g : P4 L, localizedError B x u₀ u₁ = MvPolynomial.X (1 : Fin 4) * f + MvPolynomial.X (0 : Fin 4)^2 * g := by
  have hroot : (contactMinor B u₀ u₁).IsRoot x := by
    simp only [Polynomial.IsRoot, contactMinor, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_C, h₀, h₁]
    ring
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hq₀ : shifted x (contactMinor B u₀ u₁) = MvPolynomial.X (0 : Fin 4) * shifted x q := by
    rw [hq, map_mul, shifted_X_sub_C]
  have hq₁ : shifted x (contactMinor B u₀ u₁).derivative =
      shifted x q + MvPolynomial.X (0 : Fin 4) * shifted x q.derivative := by
    rw [hq, Polynomial.derivative_mul]
    simp [Polynomial.derivative_sub, shifted_X_sub_C]
  let loc := localize L x u₀ u₁
  let y := loc (B.A * (liftX B.d0)^2 * liftX B.a1)
  let r := loc ((liftX B.d0)^2 * (liftX B.a1.derivative * B.A - liftX B.a1 * B.AX))
  let d := loc B.denominator
  let dX := loc B.denominatorX
  let T : P4 L := MvPolynomial.X (0 : Fin 4)
  let V : P4 L := MvPolynomial.X (1 : Fin 4)
  let R : P4 L := MvPolynomial.X (2 : Fin 4)
  refine ⟨y - T*r, dX * shifted x q - d * shifted x q.derivative - r*R, ?_⟩
  change localizedError B x u₀ u₁ =
    V * (y - T*r) + T^2 * (dX * shifted x q - d * shifted x q.derivative - r*R)
  calc
    _ = V * (y - T*r) - T^2*r*R + d * shifted x (contactMinor B u₀ u₁) -
        T * (d * shifted x (contactMinor B u₀ u₁).derivative -
          dX * shifted x (contactMinor B u₀ u₁)) := by
      simp only [localizedError, y, r, d, dX, loc, T, V, R,
        FlowData.yCoefficient, FlowData.rCoefficient, FlowData.denominator,
        FlowData.denominatorX, FlowData.minor, FlowData.minorX, FlowData.A, FlowData.AX,
        affine, contactMinor, Polynomial.derivative_mul, Polynomial.derivative_C,
        map_add, map_sub, map_mul, map_pow, map_zero, localize_liftX]
      simp [localize, localVariables, shifted, MvPolynomial.algebraMap_eq]
      ring
    _ = _ := by rw [hq₀, hq₁]; ring

private theorem atLeast_add_local {m : ℕ} {P Q : P4 L}
    (hP : AtLeast localWeights m P) (hQ : AtLeast localWeights m Q) :
    AtLeast localWeights m (P + Q) :=
  (MvPolynomial.restrictSupport L {e | m ≤ Finsupp.weight localWeights e}).add_mem hP hQ

theorem FlowData.contactAtLeast_flow
    (B : FlowData L) (x u₀ u₁ u : L)
    (h₀ : B.d0.eval x * u₀ + B.c0.eval x = B.a0.eval x * u)
    (h₁ : B.d0.eval x * u₁ + B.c1.eval x = B.a1.eval x * u)
    {m : ℕ} {P : P4 L} (hP : ContactAtLeast L x u₀ u₁ m P) :
    ContactAtLeast L x u₀ u₁ m (B.flow P) := by
  change AtLeast localWeights m (localize L x u₀ u₁ P) at hP
  change AtLeast localWeights m (localize L x u₀ u₁ (B.flow P))
  rw [localize_flow, localizedFlow_apply]
  have hzero (Q : P4 L) : AtLeast localWeights 0 Q := fun _ _ => Nat.zero_le _
  have hE : AtLeast localWeights 2 (localizedError B x u₀ u₁) := by
    obtain ⟨f, g, hfg⟩ := localizedError_eq B x u₀ u₁ u h₀ h₁
    rw [hfg, pow_two]
    have h1 : AtLeast localWeights 2 (MvPolynomial.X (1 : Fin 4) : P4 L) := by
      simpa [localWeights] using (atLeast_X (K := L) localWeights (1 : Fin 4))
    have h0 : AtLeast localWeights 1 (MvPolynomial.X (0 : Fin 4) : P4 L) := by
      simpa [localWeights] using (atLeast_X (K := L) localWeights (0 : Fin 4))
    exact atLeast_add_local
      (atLeast_mul localWeights h1 (hzero f))
      (atLeast_mul localWeights (atLeast_mul localWeights h0 h0) (hzero g))
  have hz := atLeast_pderiv localWeights (3 : Fin 4) hP
  have hr := atLeast_pderiv localWeights (2 : Fin 4) hP
  have hy := atLeast_pderiv localWeights (1 : Fin 4) hP
  simp [localWeights] at hz hr hy
  apply atLeast_add_local
  · simpa only [Nat.zero_add] using atLeast_add_local
      (atLeast_mul localWeights (hzero ((localize L x u₀ u₁ B.denominator)^2)) hz)
      (atLeast_mul localWeights (hzero (localize L x u₀ u₁ B.rCoefficient)) hr)
  · exact atLeast_mono localWeights (show m ≤ 2 + (m - 2) by omega)
      (atLeast_mul localWeights hE hy)

theorem FlowData.contactAtLeast_iterate_flow
    (B : FlowData L) (x u₀ u₁ u : L)
    (h₀ : B.d0.eval x * u₀ + B.c0.eval x = B.a0.eval x * u)
    (h₁ : B.d0.eval x * u₁ + B.c1.eval x = B.a1.eval x * u)
    (j : ℕ) {m : ℕ} {P : P4 L} (hP : ContactAtLeast L x u₀ u₁ m P) :
    ContactAtLeast L x u₀ u₁ m ((B.flow : P4 L → P4 L)^[j] P) := by
  induction j with
  | zero => exact hP
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact B.contactAtLeast_flow x u₀ u₁ u h₀ h₁ ih

end

end ProximityPrize.SubmissionLower.Koala6831Moving

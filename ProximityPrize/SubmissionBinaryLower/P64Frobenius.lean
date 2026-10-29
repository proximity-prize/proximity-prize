import ProximityPrize.SubmissionBinaryLower.P64NestedEval
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Perfect

namespace ProximityPrize.SubmissionBinaryLower

open Polynomial

section DerivX

variable {A : Type*} [CommRing A]

/-- Differentiate every `Y`-coefficient in its own variable (the middle `X`). -/
noncomputable def dXPoly (f : Polynomial (Polynomial A)) : Polynomial (Polynomial A) :=
  ∑ j ∈ f.support, Polynomial.monomial j (Polynomial.derivative (f.coeff j))

@[simp] theorem coeff_dXPoly (f : Polynomial (Polynomial A)) (j : ℕ) :
    (dXPoly f).coeff j = Polynomial.derivative (f.coeff j) := by
  classical
  simp only [dXPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.derivative_zero]
    · intro b hb
      have : b ≠ j := fun h => hj (h ▸ hb)
      simp [this]

theorem natDegree_dXPoly_le (f : Polynomial (Polynomial A)) :
    (dXPoly f).natDegree ≤ f.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_dXPoly, Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hj),
    Polynomial.derivative_zero]

theorem dXPoly_map {B : Type*} [CommRing B] (φ : A →+* B) (f : Polynomial (Polynomial A)) :
    (dXPoly f).map (Polynomial.mapRingHom φ) =
      dXPoly (f.map (Polynomial.mapRingHom φ)) := by
  ext1 j
  simp [Polynomial.coeff_map, Polynomial.derivative_map]

/-- Chain rule along an inseparable polynomial: if `∂f/∂Y = 0` then
`d/dX f(X, P(X)) = (∂f/∂X)(X, P(X))`. -/
theorem derivative_eval_of_derivative_eq_zero
    (f : Polynomial (Polynomial A)) (P : Polynomial A) (hf : f.derivative = 0) :
    Polynomial.derivative (f.eval P) = (dXPoly f).eval P := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self f.natDegree),
    Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_dXPoly_le f)
      (Nat.lt_succ_self f.natDegree)),
    Polynomial.derivative_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.derivative_mul, coeff_dXPoly]
  have hzero : f.coeff j * Polynomial.derivative (P ^ j) = 0 := by
    cases j with
    | zero => simp
    | succ i =>
      have h := congrArg (fun g => g.coeff i) hf
      simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h
      rw [Polynomial.derivative_pow]
      calc f.coeff (i + 1) *
            (Polynomial.C ((↑(i + 1) : A)) * P ^ (i + 1 - 1) * Polynomial.derivative P) =
          (f.coeff (i + 1) * (↑i + 1)) * (P ^ (i + 1 - 1) * Polynomial.derivative P) := by
            rw [Polynomial.C_eq_natCast]
            push_cast
            ring
        _ = 0 := by rw [h, zero_mul]
  rw [hzero, add_zero]

end DerivX

section Twist

/-!
## Frobenius twist

If `∂R/∂Y = 0` and `∂R/∂X = 0` then `R ∈ F[Z][X²][Y²]`.  Taking square roots of
the scalar coefficients and halving the `X`, `Y` exponents gives `T` with
`R(X, Y, t²) = T(X, Y, t)²` (`triEval_frobLift`).  A root `P` of `R` at `z = t²`
is then a root of `T` at `t`, and the line `U₀ + z^q U₁` becomes
`U₀ + t^{2q} U₁`.  `T` is irreducible with half the `Y`-degree.
-/

variable {F : Type} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The Frobenius square root on scalars. -/
noncomputable def sqrtF : F →+* F := ((frobeniusEquiv F 2).symm : F ≃+* F).toRingHom

@[simp] theorem sqrtF_sq (x : F) : sqrtF x ^ 2 = x := by
  have h := frobenius_apply_frobeniusEquiv_symm F 2 x
  rw [frobenius_def] at h
  exact h

theorem sqrtF_injective : Function.Injective (sqrtF : F → F) :=
  (frobeniusEquiv F 2).symm.injective

/-- Apply a coefficient map that preserves zero to every `Y`-coefficient. -/
noncomputable def mapYCoeffs {A : Type*} [CommRing A] (g : A → A)
    (f : Polynomial A) : Polynomial A :=
  ∑ j ∈ f.support, Polynomial.monomial j (g (f.coeff j))

theorem coeff_mapYCoeffs {A : Type*} [CommRing A] (g : A → A) (hg : g 0 = 0)
    (f : Polynomial A) (j : ℕ) : (mapYCoeffs g f).coeff j = g (f.coeff j) := by
  classical
  simp only [mapYCoeffs, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj, hg]
    · intro b hb
      have : b ≠ j := fun h => hj (h ▸ hb)
      simp [this]

/-- Scalar Frobenius on all coefficients, then `X ↦ X²`, then `Y ↦ Y²`. -/
noncomputable def frobLift :
    Polynomial (Polynomial (Polynomial F)) →+* Polynomial (Polynomial (Polynomial F)) :=
  (Polynomial.expand (Polynomial (Polynomial F)) 2).toRingHom.comp
    ((Polynomial.mapRingHom (Polynomial.expand (Polynomial F) 2).toRingHom).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2)))))

/-- The Frobenius twist of a polynomial in `F[Z][X²][Y²]`. -/
noncomputable def twistPoly (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (Polynomial F)) :=
  (mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R)).map
    (Polynomial.mapRingHom (Polynomial.mapRingHom sqrtF))

theorem frobLift_eq (A : Polynomial (Polynomial (Polynomial F))) :
    frobLift A = Polynomial.expand (Polynomial (Polynomial F)) 2
      ((A.map (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2)))).map
        (Polynomial.expand (Polynomial F) 2).toRingHom) := by
  simp only [frobLift, RingHom.comp_apply, Polynomial.coe_mapRingHom]
  rfl

theorem frobLift_twistPoly (R : Polynomial (Polynomial (Polynomial F)))
    (hY : R.derivative = 0) (hX : dXPoly R = 0) :
    frobLift (twistPoly R) = R := by
  have hσ : (frobenius F 2).comp (sqrtF : F →+* F) = RingHom.id F := by
    ext x
    exact frobenius_apply_frobeniusEquiv_symm F 2 x
  have h2 : (Polynomial.mapRingHom (frobenius F 2)).comp
      (Polynomial.mapRingHom (sqrtF : F →+* F)) = RingHom.id _ := by
    rw [Polynomial.mapRingHom_comp, hσ, Polynomial.mapRingHom_id]
  have hcomp : (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2))).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (sqrtF : F →+* F))) =
      RingHom.id _ := by
    rw [Polynomial.mapRingHom_comp, h2, Polynomial.mapRingHom_id]
  have hR1 : (mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R)).map
      (Polynomial.expand (Polynomial F) 2).toRingHom = Polynomial.contract 2 R := by
    ext1 j
    rw [Polynomial.coeff_map, coeff_mapYCoeffs _ (by ext n; rw [Polynomial.coeff_contract (by norm_num)]; simp)]
    have hd : Polynomial.derivative ((Polynomial.contract 2 R).coeff j) = 0 := by
      rw [Polynomial.coeff_contract (by norm_num)]
      rw [← coeff_dXPoly, hX, Polynomial.coeff_zero]
    exact Polynomial.expand_contract 2 hd (by norm_num)
  have hback : ((mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R)).map
      (Polynomial.mapRingHom (Polynomial.mapRingHom (sqrtF : F →+* F)))).map
        (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2))) =
      mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R) := by
    rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  rw [frobLift_eq]
  unfold twistPoly
  rw [hback, hR1]
  exact Polynomial.expand_contract 2 hY (by norm_num)

/-- Squaring a value of `B(X, Q)` is evaluating the Frobenius-twisted `B` at `Q²`. -/
theorem eval_map_frobenius_sq (B : Polynomial (Polynomial F)) (Q : Polynomial F) :
    (B.map (frobenius (Polynomial F) 2)).eval (Q ^ 2) = (B.eval Q) ^ 2 := by
  calc (B.map (frobenius (Polynomial F) 2)).eval (Q ^ 2) =
        B.eval₂ ((frobenius (Polynomial F) 2).comp (RingHom.id _))
          (frobenius (Polynomial F) 2 Q) := by
        rw [Polynomial.eval_map, frobenius_def]
        rfl
    _ = frobenius (Polynomial F) 2 (B.eval₂ (RingHom.id _) Q) :=
        (Polynomial.hom_eval₂ B (RingHom.id _) (frobenius (Polynomial F) 2) Q).symm
    _ = (B.eval Q) ^ 2 := by
        rw [frobenius_def]
        rfl

/-- The key identity `R(X, Y, t²) = T(X, Y, t)²`. -/
theorem triEval_frobLift (A : Polynomial (Polynomial (Polynomial F))) (t : F)
    (P : Polynomial F) :
    triEval (frobLift A) (t ^ 2) P = (triEval A t P) ^ 2 := by
  have hhom : ((Polynomial.mapRingHom (Polynomial.evalRingHom (t ^ 2))).comp
      (Polynomial.expand (Polynomial F) 2).toRingHom).comp
        (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2))) =
      (frobenius (Polynomial F) 2).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom t)) := by
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.expand_C,
        Polynomial.coe_evalRingHom, frobenius_def, ← Polynomial.C_pow]
      congr 1
      have h := Polynomial.hom_eval₂ b (RingHom.id F) (frobenius F 2) t
      rw [Polynomial.eval_map]
      simp only [frobenius_def] at h
      rw [show (frobenius F 2).comp (RingHom.id F) = frobenius F 2 from rfl] at h
      rw [show Polynomial.eval t b = Polynomial.eval₂ (RingHom.id F) t b from rfl, h]
    · simp [frobenius_def]
  unfold triEval
  rw [frobLift_eq, Polynomial.map_expand, Polynomial.expand_eval, Polynomial.map_map,
    Polynomial.map_map, hhom, ← Polynomial.map_map]
  exact eval_map_frobenius_sq _ P

theorem natDegree_frobLift (A : Polynomial (Polynomial (Polynomial F))) :
    (frobLift A).natDegree = A.natDegree * 2 := by
  rw [frobLift_eq, Polynomial.natDegree_expand]
  congr 1
  rw [Polynomial.natDegree_map_eq_of_injective, Polynomial.natDegree_map_eq_of_injective]
  · exact Polynomial.map_injective _ (Polynomial.map_injective _ (frobenius_inj F 2))
  · exact Polynomial.expand_injective (by norm_num)

theorem coeff_coeff_frobLift (A : Polynomial (Polynomial (Polynomial F))) (j a : ℕ) :
    ((frobLift A).coeff (j * 2)).coeff (a * 2) =
      ((A.coeff j).coeff a).map (frobenius F 2) := by
  rw [frobLift_eq, Polynomial.coeff_expand_mul (by norm_num), Polynomial.coeff_map,
    Polynomial.coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [Polynomial.coeff_expand_mul (by norm_num), Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  rfl

theorem isUnit_of_isUnit_frobLift (A : Polynomial (Polynomial (Polynomial F)))
    (h : IsUnit (frobLift A)) : IsUnit A := by
  have h0 : A.natDegree = 0 := by
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [natDegree_frobLift] at this
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at h ⊢
  rw [Polynomial.isUnit_C]
  set a₀ := A.coeff 0
  have h1 : IsUnit ((a₀.map (Polynomial.mapRingHom (frobenius F 2))).map
      (Polynomial.expand F 2).toRingHom |> fun x => Polynomial.expand (Polynomial F) 2
        (a₀.map (Polynomial.mapRingHom (frobenius F 2)))) := by
    simpa [frobLift_eq] using h
  have h1' : IsUnit (Polynomial.expand (Polynomial F) 2
      (a₀.map (Polynomial.mapRingHom (frobenius F 2)))) := h1
  have hdeg1 := Polynomial.natDegree_eq_zero_of_isUnit h1'
  rw [Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective
    (Polynomial.map_injective _ (frobenius_inj F 2))] at hdeg1
  have ha0 : a₀.natDegree = 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero ha0] at h1' ⊢
  rw [Polynomial.isUnit_C]
  set b₀ := a₀.coeff 0
  have h2 : IsUnit (b₀.map (frobenius F 2)) := by
    simpa [Polynomial.isUnit_C] using h1'
  have hdeg2 := Polynomial.natDegree_eq_zero_of_isUnit h2
  rw [Polynomial.natDegree_map_eq_of_injective (frobenius_inj F 2)] at hdeg2
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg2] at h2 ⊢
  rw [Polynomial.isUnit_C]
  rw [Polynomial.map_C, Polynomial.isUnit_C] at h2
  rw [isUnit_iff_ne_zero] at h2 ⊢
  intro hz
  apply h2
  rw [hz, map_zero]

theorem irreducible_twistPoly (R : Polynomial (Polynomial (Polynomial F)))
    (hirr : Irreducible R) (hY : R.derivative = 0) (hX : dXPoly R = 0) :
    Irreducible (twistPoly R) := by
  have hR := frobLift_twistPoly R hY hX
  refine ⟨?_, ?_⟩
  · intro hu
    apply hirr.not_isUnit
    rw [← hR]
    exact hu.map frobLift
  · intro a b hab
    have h := hirr.isUnit_or_isUnit (show R = frobLift a * frobLift b by
      rw [← hR, hab, map_mul])
    rcases h with h | h
    · exact Or.inl (isUnit_of_isUnit_frobLift a h)
    · exact Or.inr (isUnit_of_isUnit_frobLift b h)

end Twist

end ProximityPrize.SubmissionBinaryLower

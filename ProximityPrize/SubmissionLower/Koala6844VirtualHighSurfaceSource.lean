import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6844Comparison
import ProximityPrize.SubmissionLower.Koala6844ActiveGerm
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSpecialization


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial Koala6844Normalization Koala6844BivariateSeeds RCN132 RCN136
open scoped Classical Matrix

noncomputable section

set_option autoImplicit false

variable {K E I : Type} [Field K] [Field E]

def fractionValue (P : Polynomial E) : RationalCoefficients E :=
  algebraMap (Polynomial E) (RationalCoefficients E) P

def fractionConstant (s : E) : RationalCoefficients E :=
  fractionValue (Polynomial.C s)

theorem eval_surface_eq_fraction_specialize (P : Polynomial E) (s t : E)
    (F : MvPolynomial (Fin 4) E) :
    MvPolynomial.eval (Fin.cases (fractionValue P)
      (coordinates (fractionConstant s) (fractionConstant t))) (rationalSurfaceMap E F) =
      fractionValue (specializeGerm P s t (MvPolynomial.finSuccEquiv E 3 F)) := by
  let φ := algebraMap (Polynomial E) (RationalCoefficients E)
  let z : Fin 3 → RationalCoefficients E := Fin.cases (fractionValue P) (coordinates (fractionConstant s) (fractionConstant t))
  have h : (MvPolynomial.eval z).comp (rationalSurfaceMap E) =
      φ.comp (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P, Polynomial.C s, Polynomial.C t]) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rationalSurfaceMap, φ]
    · intro i
      fin_cases i
      · simp [rationalSurfaceMap, φ]
      · change (MvPolynomial.eval z) (surfaceMap φ (MvPolynomial.X (Fin.succ (0 : Fin 3)))) = _
        rw [surfaceMap_X_succ]
        simp [z, φ, coordinates, fractionValue, fractionConstant, Matrix.cons_val_two, Matrix.cons_val_three]
      · change (MvPolynomial.eval z) (surfaceMap φ (MvPolynomial.X (Fin.succ (1 : Fin 3)))) = _
        rw [surfaceMap_X_succ]
        simp [z, φ, coordinates, fractionValue, fractionConstant, Matrix.cons_val_two, Matrix.cons_val_three]
        change coordinates (φ (Polynomial.C s)) (φ (Polynomial.C t)) (0 : Fin 2) = _
        simp [coordinates, φ]
      · change (MvPolynomial.eval z) (surfaceMap φ (MvPolynomial.X (Fin.succ (2 : Fin 3)))) = _
        rw [surfaceMap_X_succ]
        simp [z, φ, coordinates, fractionValue, fractionConstant, Matrix.cons_val_two, Matrix.cons_val_three]
        change coordinates (φ (Polynomial.C s)) (φ (Polynomial.C t)) (1 : Fin 2) = _
        simp [coordinates, φ]
  change (MvPolynomial.eval z) (rationalSurfaceMap E F) =
    φ (specializeGerm P s t (MvPolynomial.finSuccEquiv E 3 F))
  replace h := DFunLike.congr_fun h F
  have h' := DFunLike.congr_fun (specialize_finSuccEquiv P s t) F
  exact h.trans (congrArg φ h').symm

variable [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem mapped_normalized_fraction_injOn
    (D : CenteredVirtualData x nodes σ w agreement errors excess) (embed : K →+* E) :
    Set.InjOn (fun g => fractionValue ((D.normalized g).map embed)) (↑D.seeds : Set K) := by
  intro g hg h hh eq
  apply Koala6844ActiveGerm.normalized_injOn D hg hh
  apply (Polynomial.map_injective embed embed.injective)
  exact IsFractionRing.injective (Polynomial E) (RationalCoefficients E) eq

theorem eval_mapped_centered_surface_eq_zero
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (p : ℕ) (hσ : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p)
    (F : MvPolynomial (Fin 4) E)
    (hz : ∀ g ∈ D.seeds, specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g))
      (MvPolynomial.finSuccEquiv E 3 F) = 0) :
    ∀ g ∈ D.seeds, MvPolynomial.eval
      (Fin.cases (fractionValue ((D.normalized g).map embed))
        (coordinates (fractionConstant (embed g)) ((fractionConstant (embed g)) ^ p)))
      (rationalSurfaceMap E F) = 0 := by
  intro g hg
  have hpow : fractionConstant (embed (σ g)) = fractionConstant (embed g) ^ p := by
    rw [hσ g hg]
    simp [fractionConstant, fractionValue]
  rw [← hpow, eval_surface_eq_fraction_specialize, hz g hg]
  exact map_zero _

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

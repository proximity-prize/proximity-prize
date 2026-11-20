import ProximityPrize.SubmissionLower.Koala6831IntrinsicChart

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open RCN002 RCN135 RCN136

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 20000

variable {K L : Type} [Field K] [Field L]

def polynomialGraphSurfacePoint (φ : Polynomial K →+* L) (P : Polynomial K)
    (z₀ z₁ : K) : Fin 3 → L :=
  ![φ P, φ (Polynomial.C z₀), φ (Polynomial.C z₁)]

theorem eval_polynomialGraphSurfacePoint (φ : Polynomial K →+* L) (P : Polynomial K)
    (z₀ z₁ : K) (Q : Carrier K) :
    MvPolynomial.eval (polynomialGraphSurfacePoint φ P z₀ z₁) (surfaceMap φ Q) =
      φ (graphSpecialize P z₀ z₁ Q) := by
  rw [eval_surfaceMap]
  have h : MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (Fin.cases (φ Polynomial.X) (polynomialGraphSurfacePoint φ P z₀ z₁)) =
      φ.comp (graphSpecialize P z₀ z₁) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [graphSpecialize]
    · intro i
      fin_cases i <;> simp [graphSpecialize, polynomialGraphSurfacePoint, Fin.cases] <;> rfl
  exact DFunLike.congr_fun h Q

theorem polynomialGraphSurfacePoint_tail_zero (φ : Polynomial K →+* L)
    (F : Carrier K) (P : Polynomial K) (z₀ z₁ : K)
    (hF : graphSpecialize P z₀ z₁ F = 0) (j : ℕ) (hP : P.natDegree ≤ j) :
    MvPolynomial.eval (polynomialGraphSurfacePoint φ P z₀ z₁)
      (surfaceMap φ (tailNumerator F j)) = 0 := by
  rw [eval_polynomialGraphSurfacePoint,
    graphSpecialize_tailNumerator_eq_zero F P z₀ z₁ hF j hP, map_zero]

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic

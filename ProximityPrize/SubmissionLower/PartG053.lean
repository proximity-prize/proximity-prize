import ProximityPrize.SubmissionLower.PartG052


section Compact_SecondJetMovingDegree
/-! Turning the weighted root-height estimate into the integer degree of a
separable moving coordinate; no rounding is charged per component. -/
namespace ProximityPrize.SubmissionLower.SecondJetMovingDegree
open scoped BigOperators
open RCN026 RCN095 RCN187 RCN204 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]

theorem exists_exact_pole_sum (c : SeparableCoordinate K L) :
    ∃ V : Finset (RCN026.Place K L),
      (∑ v ∈ V, poleOrder v.val (SeparableCoordinate.value K L c)) =
        (SeparableCoordinate.degree K L c : ℤ) := by
  letI : Algebra (RatFunc K) L := c.embedding.toRingHom.toAlgebra
  letI : Algebra (Polynomial K) L :=
    (c.embedding.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
  letI : IsScalarTower (Polynomial K) (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq fun a => (c.embedding.commutes a).symm
  letI : IsScalarTower K (Polynomial K) L :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K L a =
        c.embedding (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) a))
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      exact (c.embedding.commutes a).symm
  letI : FiniteDimensional (RatFunc K) L := c.finite
  letI : Algebra.IsSeparable (RatFunc K) L := c.separable
  refine ⟨RCN346.infinityValues K L,?_⟩
  exact RCN346.sum_poles_infinityValues_eq_finrank K L

variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem degree_bound (P : SecondJetSupport.Poly (K := K)) (freezeX : K)
    (B U T d n0 : ℕ) (hBU : B ≤ U) (hUT : U ≤ T) (hdn : d ≤ n0)
    (hB : 2*(n0-d) ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (x : Fin 3 → L) (Q : Polynomial L)
    (hQcoeff : ∀ j, Q.coeff j = MvPolynomial.eval₂Hom (algebraMap K L) x
      (SecondJetFlagCoefficients.freeze freezeX ((SecondJetCoefficients.asS P).coeff j)))
    (hQ : Q ≠ 0) (hn : n0 ≤ Q.natDegree) (t : L)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ Q)
    (J : SeparableCoordinate K L)
    (hJ : ∀ v : RCN026.Place K L,
      poleOrder v.val (SeparableCoordinate.value K L J) =
        max (2*flagPole v.val x unitAllFlag)
          (flagPole v.val x unitYZFlag+poleOrder v.val t))
    (C : ℤ) (hbudget : ∀ V : Finset (RCN026.Place K L),
      (∑ v ∈ V, flagPole v.val x (SecondJetRelaxedFlag.budgetFlag B U T d n0)) ≤ C) :
    (d : ℤ)*(SeparableCoordinate.degree K L J : ℤ) ≤ C := by
  obtain ⟨V,hV⟩ := exists_exact_pole_sum K L J
  have hh := SecondJetRelaxedFlag.moving_bound P freezeX B U T d n0 hBU hUT hdn hB
    hP x Q hQcoeff hQ hn t hd C hbudget V
  have he : (∑ v ∈ V, max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t)) =
      (SeparableCoordinate.degree K L J : ℤ) := by
    simpa only [← hJ] using hV
  rwa [he] at hh

end
end ProximityPrize.SubmissionLower.SecondJetMovingDegree

end Compact_SecondJetMovingDegree

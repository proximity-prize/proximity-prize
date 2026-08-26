import ProximityPrize.SubmissionLower.BCHKSFiniteHensel
namespace ProximityPrize.SubmissionLower
open Polynomial
open Polynomial.Bivariate
variable {F : Type} [Field F]
noncomputable def mapBivariateToRatFunc (H : F[X][Y]) : (RatFunc F)[X] :=
  H.map (algebraMap F[X] (RatFunc F))
abbrev AdjoinedRootField (H : F[X][Y]) :=
  AdjoinRoot (mapBivariateToRatFunc H)
noncomputable def adjoinedAlpha (H : F[X][Y]) : AdjoinedRootField H :=
  AdjoinRoot.root (mapBivariateToRatFunc H)
theorem mapBivariateToRatFunc_eval₂_adjoinedAlpha (H : F[X][Y]) :
    (mapBivariateToRatFunc H).eval₂
      (AdjoinRoot.of (mapBivariateToRatFunc H)) (adjoinedAlpha H) = 0 := by
  exact AdjoinRoot.eval₂_root (mapBivariateToRatFunc H)
theorem adjoinedRootField_isField_of_irreducible (H : F[X][Y])
    (hirr : Irreducible (mapBivariateToRatFunc H)) :
    Nonempty (Field (AdjoinedRootField H)) := by
  letI : Fact (Irreducible (mapBivariateToRatFunc H)) := ⟨hirr⟩
  exact ⟨inferInstance⟩
noncomputable def adjoinedSlope (H : F[X][Y]) : AdjoinedRootField H :=
  (mapBivariateToRatFunc H).derivative.eval₂
    (AdjoinRoot.of (mapBivariateToRatFunc H)) (adjoinedAlpha H)
theorem adjoinedAlpha_isSimpleRoot (H : F[X][Y])
    (hslope : adjoinedSlope H ≠ 0) :
    (mapBivariateToRatFunc H).eval₂
        (AdjoinRoot.of (mapBivariateToRatFunc H)) (adjoinedAlpha H) = 0 ∧
      adjoinedSlope H ≠ 0 :=
  ⟨mapBivariateToRatFunc_eval₂_adjoinedAlpha H, hslope⟩
noncomputable def mapTrivariateToAdjoinedRoot
    (H : F[X][Y]) [Fact (Irreducible (mapBivariateToRatFunc H))]
    (R : Polynomial (Polynomial (Polynomial F))) :
    (AdjoinedRootField H)[X][Y] :=
  (Trivariate.toRatFuncPoly R).map
    (Polynomial.mapRingHom (AdjoinRoot.of (mapBivariateToRatFunc H)))
noncomputable def specializeXZeroRatFunc
    (R : (RatFunc F)[X][Y]) : (RatFunc F)[X] :=
  R.map (Polynomial.evalRingHom 0)
theorem eval₂_specializeXZero_eq_zero_of_dvd
    (H : F[X][Y]) [Fact (Irreducible (mapBivariateToRatFunc H))]
    (R : (RatFunc F)[X][Y])
    (hdiv : mapBivariateToRatFunc H ∣ specializeXZeroRatFunc R) :
    (specializeXZeroRatFunc R).eval₂
      (AdjoinRoot.of (mapBivariateToRatFunc H)) (adjoinedAlpha H) = 0 := by
  rcases hdiv with ⟨Q, hQ⟩
  rw [hQ, Polynomial.eval₂_mul]
  rw [mapBivariateToRatFunc_eval₂_adjoinedAlpha]
  simp
section AbstractHensel
variable {L : Type} [Field L]
noncomputable def henselJet (R : L[X][Y]) (α₀ slope : L) : ℕ → L[X]
  | 0 => Polynomial.C α₀
  | n + 1 =>
      let P := henselJet R α₀ slope n
      let c := -((R.eval P).coeff (n + 1)) / slope
      P + Polynomial.monomial (n + 1) c
noncomputable def henselCorrection (R : L[X][Y]) (α₀ slope : L) (n : ℕ) : L :=
  -((R.eval (henselJet R α₀ slope n)).coeff (n + 1)) / slope
theorem henselJet_succ (R : L[X][Y]) (α₀ slope : L) (n : ℕ) :
    henselJet R α₀ slope (n + 1) =
      henselJet R α₀ slope n +
        Polynomial.monomial (n + 1) (henselCorrection R α₀ slope n) := by
  rfl
def VanishesThrough (R : L[X][Y]) (P : L[X]) (N : ℕ) : Prop :=
  ∀ j ≤ N, (R.eval P).coeff j = 0
theorem henselJet_vanishesThrough
    (R : L[X][Y]) (α₀ slope : L) (N : ℕ)
    (hslope : slope ≠ 0)
    (hbase : (R.eval (Polynomial.C α₀)).coeff 0 = 0)
    (hstable : ∀ n j, j ≤ n →
      (R.eval (henselJet R α₀ slope (n + 1))).coeff j =
        (R.eval (henselJet R α₀ slope n)).coeff j)
    (hlinear : ∀ n,
      (R.eval (henselJet R α₀ slope (n + 1))).coeff (n + 1) =
        (R.eval (henselJet R α₀ slope n)).coeff (n + 1) +
          slope * henselCorrection R α₀ slope n) :
    VanishesThrough R (henselJet R α₀ slope N) N := by
  induction N with
  | zero =>
      intro j hj
      have : j = 0 := by omega
      subst j
      exact hbase
  | succ n ih =>
      intro j hj
      by_cases hjn : j ≤ n
      · rw [hstable n j hjn]
        exact ih j hjn
      · have hj' : j = n + 1 := by omega
        subst j
        rw [hlinear]
        simp only [henselCorrection]
        field_simp
        ring
theorem henselJet_coeff_zero (R : L[X][Y]) (α₀ slope : L) (n : ℕ) :
    (henselJet R α₀ slope n).coeff 0 = α₀ := by
  induction n with
  | zero => simp [henselJet]
  | succ n ih =>
      rw [henselJet_succ, Polynomial.coeff_add, Polynomial.coeff_monomial]
      simp [ih]
end AbstractHensel
theorem exists_adjoined_root_hensel_jet
    (H : F[X][Y]) [Fact (Irreducible (mapBivariateToRatFunc H))]
    (R : (AdjoinedRootField H)[X][Y])
    (slope : AdjoinedRootField H) (N : ℕ)
    (hslope : slope ≠ 0)
    (hbase : (R.eval (Polynomial.C (adjoinedAlpha H))).coeff 0 = 0)
    (hstable : ∀ n j, j ≤ n →
      (R.eval (henselJet R (adjoinedAlpha H) slope (n + 1))).coeff j =
        (R.eval (henselJet R (adjoinedAlpha H) slope n)).coeff j)
    (hlinear : ∀ n,
      (R.eval (henselJet R (adjoinedAlpha H) slope (n + 1))).coeff (n + 1) =
        (R.eval (henselJet R (adjoinedAlpha H) slope n)).coeff (n + 1) +
          slope * henselCorrection R (adjoinedAlpha H) slope n) :
    ∃ P : (AdjoinedRootField H)[X],
      P.coeff 0 = adjoinedAlpha H ∧ VanishesThrough R P N := by
  refine ⟨henselJet R (adjoinedAlpha H) slope N,
    henselJet_coeff_zero R (adjoinedAlpha H) slope N, ?_⟩
  exact henselJet_vanishesThrough R (adjoinedAlpha H) slope N hslope hbase hstable hlinear
theorem exists_adjoined_finiteHenselLift
    (H : F[X][Y]) [Fact (Irreducible (mapBivariateToRatFunc H))]
    (R : Polynomial (Polynomial (AdjoinedRootField H)))
    (hsimple : FiniteHensel.IsSimpleRootAt R 0 (adjoinedAlpha H)) (N : ℕ) :
    ∃ c : ℕ → AdjoinedRootField H,
      c 0 = adjoinedAlpha H ∧
      FiniteHensel.VanishesThrough
        (FiniteHensel.residual R 0 c N) N := by
  exact FiniteHensel.exists_finiteHenselLift R 0 (adjoinedAlpha H) N hsimple
end ProximityPrize.SubmissionLower

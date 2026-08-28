import ProximityPrize.SubmissionLower.BCHKSAdjoinLift
import ProximityPrize.SubmissionLower.BCHKSFiniteLiftExact

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions

variable {F : Type} [Field F]

/-- The ground-field embedding into the adjoined algebraic function field. -/
noncomputable def baseToAdjoined (H : F[X][Y]) : F →+* AdjoinedRootField H :=
  (AdjoinRoot.of (mapBivariateToRatFunc H)).comp (algebraMap F (RatFunc F))

/-- Lagrange interpolation on exactly `k+1` nodes has degree at most `k`. -/
theorem lagrange_natDegree_le_of_card_eq_succ
    [DecidableEq F] (E : Finset F) (U : F → F) (k : ℕ) (hcard : E.card = k + 1) :
    (Lagrange.interpolate E id U).natDegree ≤ k := by
  classical
  let p := Lagrange.interpolate E id U
  change p.natDegree ≤ k
  by_cases hp : p = 0
  · rw [hp]
    simp
  · have hdeg : p.degree < (E.card : WithBot ℕ) :=
      Lagrange.degree_interpolate_lt U (Set.injOn_id (↑E : Set F))
    have hnat : p.natDegree < E.card :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg
    simpa [hcard] using hnat

/-- Final interpolation identity in the algebraic function field.

Choose `k+1` nodes from `D`, interpolate the two ground-field rows there, and
use polynomial uniqueness over the extension field to identify `γ` with their
affine combination in the distinguished algebraic parameter. -/
theorem adjoinedRoot_polynomial_eq_affine_of_many_evals
    [DecidableEq F] (H : F[X][Y]) [Fact (Irreducible (mapBivariateToRatFunc H))]
    (γ : (AdjoinedRootField H)[X]) (k : ℕ)
    (D : Finset F) (hD : k + 1 ≤ D.card) (U₀ U₁ : F → F)
    (hγdeg : γ.natDegree ≤ k)
    (heval : ∀ x ∈ D,
      γ.eval (baseToAdjoined H x) =
        baseToAdjoined H (U₀ x) +
          adjoinedAlpha H * baseToAdjoined H (U₁ x)) :
    ∃ E : Finset F, E ⊆ D ∧ E.card = k + 1 ∧
      let p₀ := Lagrange.interpolate E id U₀
      let p₁ := Lagrange.interpolate E id U₁
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      γ = p₀.map (baseToAdjoined H) +
        Polynomial.C (adjoinedAlpha H) * p₁.map (baseToAdjoined H) := by
  classical
  obtain ⟨E, hED, hEcard⟩ := Finset.exists_subset_card_eq hD
  refine ⟨E, hED, hEcard, ?_⟩
  let p₀ : F[X] := Lagrange.interpolate E id U₀
  let p₁ : F[X] := Lagrange.interpolate E id U₁
  have hp₀deg : p₀.natDegree ≤ k :=
    lagrange_natDegree_le_of_card_eq_succ E U₀ k hEcard
  have hp₁deg : p₁.natDegree ≤ k :=
    lagrange_natDegree_le_of_card_eq_succ E U₁ k hEcard
  refine ⟨hp₀deg, hp₁deg, ?_⟩
  let rhs : (AdjoinedRootField H)[X] :=
    p₀.map (baseToAdjoined H) +
      Polynomial.C (adjoinedAlpha H) * p₁.map (baseToAdjoined H)
  have hrhsdeg : rhs.natDegree ≤ k := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_map_le.trans hp₀deg
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_map_le.trans hp₁deg)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq γ rhs
    (f := fun x : E => baseToAdjoined H (x : F))
  · exact (RingHom.injective (baseToAdjoined H)).comp Subtype.val_injective
  · intro x
    have hxD : (x : F) ∈ D := hED x.property
    have hp₀eval : p₀.eval (x : F) = U₀ x := by
      exact Lagrange.eval_interpolate_at_node U₀ (Set.injOn_id (↑E : Set F)) x.property
    have hp₁eval : p₁.eval (x : F) = U₁ x := by
      exact Lagrange.eval_interpolate_at_node U₁ (Set.injOn_id (↑E : Set F)) x.property
    rw [heval x hxD]
    simp [rhs, Polynomial.eval_add, Polynomial.eval_mul, hp₀eval, hp₁eval,
      Polynomial.eval_map]
  · rw [Fintype.card_coe, hEcard]
    exact max_lt (hγdeg.trans_lt (Nat.lt_succ_self k))
      (hrhsdeg.trans_lt (Nat.lt_succ_self k))

/-- Specialization finish.  `specialized_truncSeries_eq_shift` supplies the
left equality from finite-Hensel uniqueness; the remaining hypothesis is the
explicit specialization of the algebraic affine identity. -/
theorem specialized_polynomial_eq_affine_shift
    {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z)
    (β : ℕ → 𝒪 H) (Cden : ℕ → F[X])
    (R : F[X][Y]) (Pz p₀ p₁ : F[X]) (x₀ y₀ : F) (k : ℕ)
    (hdeg : Pz.natDegree ≤ k) (hExact : R.eval Pz = 0)
    (hsimple : FiniteHensel.IsSimpleRootAt R x₀ y₀)
    (ha0 : piZOfDiv z root (β 0) (Cden 0) = y₀)
    (hP0 : Pz.eval x₀ = y₀)
    (hvanish : FiniteHensel.VanishesThrough
      (FiniteHensel.residual R x₀
        (fun n => piZOfDiv z root (β n) (Cden n)) k) k)
    (haffineSpecialization :
      FiniteHensel.truncSeries
        (fun n => piZOfDiv z root (β n) (Cden n)) k =
      p₀ + Polynomial.C z * p₁) :
    Pz.comp (Polynomial.C x₀ + Polynomial.X) =
      p₀ + Polynomial.C z * p₁ := by
  rw [← haffineSpecialization]
  exact (specialized_truncSeries_eq_shift z root β Cden R Pz x₀ y₀ k
    hdeg hExact hsimple ha0 hP0 hvanish).symm

/-- At expansion point zero, the shifted conclusion is the ordinary affine
identity `Pz = p₀ + z p₁`. -/
theorem specialized_polynomial_eq_affine
    {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z)
    (β : ℕ → 𝒪 H) (Cden : ℕ → F[X])
    (R : F[X][Y]) (Pz p₀ p₁ : F[X]) (y₀ : F) (k : ℕ)
    (hdeg : Pz.natDegree ≤ k) (hExact : R.eval Pz = 0)
    (hsimple : FiniteHensel.IsSimpleRootAt R 0 y₀)
    (ha0 : piZOfDiv z root (β 0) (Cden 0) = y₀)
    (hP0 : Pz.eval 0 = y₀)
    (hvanish : FiniteHensel.VanishesThrough
      (FiniteHensel.residual R 0
        (fun n => piZOfDiv z root (β n) (Cden n)) k) k)
    (haffineSpecialization :
      FiniteHensel.truncSeries
        (fun n => piZOfDiv z root (β n) (Cden n)) k =
      p₀ + Polynomial.C z * p₁) :
    Pz = p₀ + Polynomial.C z * p₁ := by
  have h := specialized_polynomial_eq_affine_shift z root β Cden R Pz p₀ p₁
    0 y₀ k hdeg hExact hsimple ha0 hP0 hvanish haffineSpecialization
  simpa using h

end ProximityPrize.SubmissionLower

import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminantSpan6400
import ProximityPrize.SubmissionLower.BCHKSLocatorLowCandidateObstruction6400

/-!
# From a low pair determinant to a bounded locator obstruction

This module connects the rank-two polynomial-pair argument to the checked
rank-drop/Cramer pipeline.  A nonzero low-degree determinant of two vectors
in the fraction-field span of a finite polynomial pair family is first
returned to the span of the original pairwise determinant candidates.  Its
vanishing high coefficients then force the strict rank drop from which the
bounded obstruction is extracted.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

variable {F : Type} [Field F]

theorem degreeLT_mem_span_of_coe_mem_span
    {K I : Type} [Field K] [Fintype I] {D : ℕ}
    (family : I → Polynomial.degreeLT K D)
    (w : Polynomial.degreeLT K D)
    (hw : w.1 ∈ Submodule.span K (Set.range fun i => (family i).1)) :
    w ∈ Submodule.span K (Set.range family) := by
  let f : Polynomial.degreeLT K D →ₗ[K] K[X] :=
    (Polynomial.degreeLT K D).subtype
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp
    (Polynomial.degreeLT K D).ker_subtype
  rw [← (Submodule.apply_mem_span_image_iff_mem_span
    (f := f) (x := w) (s := Set.range family) hf)]
  have himage : f '' Set.range family =
      Set.range (fun i => f (family i)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨family i, ⟨i, rfl⟩, rfl⟩
  rw [himage]
  simpa [f] using hw

noncomputable def locatorPairDetCandidate
    {I : Type} (A B : I → F[X][X]) (ij : I × I) : F[X][X] :=
  A ij.1 * B ij.2 - B ij.1 * A ij.2

noncomputable def locatorPairFamilyFraction
    {I : Type} (c h : ℕ) (A B : I → F[X][X])
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h) :
    I → PolynomialPairSpace (FractionRing F[X]) c h :=
  fun i =>
    (locatorFractionDegreeLT c (A i) (hA i),
      locatorFractionDegreeLT h (B i) (hB i))

theorem polynomialPairDet_locatorPairFamilyFraction
    {I : Type} (c h : ℕ) (A B : I → F[X][X])
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h)
    (i j : I) :
    polynomialPairDet
        (locatorPairFamilyFraction c h A B hA hB i)
        (locatorPairFamilyFraction c h A B hA hB j) =
      (locatorPairDetCandidate A B (i, j)).map
        (algebraMap F[X] (FractionRing F[X])) := by
  simp [locatorPairFamilyFraction, polynomialPairDet,
    locatorFractionDegreeLT, locatorPairDetCandidate]

theorem exists_bounded_locatorCramerObstruction_of_pair_span_det_with_span
    {I : Type} [Fintype I]
    {c h D l S : ℕ} (A B : I → F[X][X])
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h)
    (hbounded : ∀ ij, locatorPairDetCandidate A B ij ∈
      Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ ij n,
      ((locatorPairDetCandidate A B ij).coeff n).natDegree ≤ S)
    (hlD : l ≤ D)
    (u v : PolynomialPairSpace (FractionRing F[X]) c h)
    (hu : u ∈ Submodule.span (FractionRing F[X])
      (Set.range (locatorPairFamilyFraction c h A B hA hB)))
    (hv : v ∈ Submodule.span (FractionRing F[X])
      (Set.range (locatorPairFamilyFraction c h A B hA hB)))
    (hdetne : polynomialPairDet u v ≠ 0)
    (hdetdegree : (polynomialPairDet u v).natDegree < l) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X]
        (Set.range (locatorPairDetCandidate A B)) := by
  classical
  let K := FractionRing F[X]
  let family : I → PolynomialPairSpace K c h :=
    locatorPairFamilyFraction c h A B hA hB
  let candidate : I × I → F[X][X] := locatorPairDetCandidate A B
  have hdetBound : polynomialPairDet u v ∈ Polynomial.degreeLT K D := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Polynomial.natDegree_lt_iff_degree_lt hdetne] at hdetdegree
    exact hdetdegree.trans_le (WithBot.coe_le_coe.mpr hlD)
  let w : Polynomial.degreeLT K D := ⟨polynomialPairDet u v, hdetBound⟩
  have hdetSpan := polynomialPairDet_mem_span_pairwise family u v
    (by simpa [family, K] using hu) (by simpa [family, K] using hv)
  have hcoeSpan : w.1 ∈ Submodule.span K (Set.range
      (fun ij : I × I =>
        (locatorFractionDegreeLT D (candidate ij) (hbounded ij)).1)) := by
    simpa [w, family, candidate, K,
      polynomialPairDet_locatorPairFamilyFraction,
      locatorFractionDegreeLT] using hdetSpan
  have hwspan : w ∈ Submodule.span K (Set.range
      (fun ij : I × I =>
        locatorFractionDegreeLT D (candidate ij) (hbounded ij))) :=
    degreeLT_mem_span_of_coe_mem_span _ _ hcoeSpan
  have hwne : w ≠ 0 := by
    intro hw
    apply hdetne
    exact congrArg (fun y : Polynomial.degreeLT K D => (y.1 : K[X])) hw
  have hwker : locatorFractionHighPart D l w = 0 := by
    funext t
    change (polynomialPairDet u v).coeff (l + t.1) = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  exact exists_bounded_locatorCramerObstruction_of_span_kernel_with_span
    candidate hbounded hcoeff w hwspan hwne hwker

/-- Compatibility wrapper which forgets the inherited pair-determinant span
membership. -/
theorem exists_bounded_locatorCramerObstruction_of_pair_span_det
    {I : Type} [Fintype I]
    {c h D l S : ℕ} (A B : I → F[X][X])
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h)
    (hbounded : ∀ ij, locatorPairDetCandidate A B ij ∈
      Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ ij n,
      ((locatorPairDetCandidate A B ij).coeff n).natDegree ≤ S)
    (hlD : l ≤ D)
    (u v : PolynomialPairSpace (FractionRing F[X]) c h)
    (hu : u ∈ Submodule.span (FractionRing F[X])
      (Set.range (locatorPairFamilyFraction c h A B hA hB)))
    (hv : v ∈ Submodule.span (FractionRing F[X])
      (Set.range (locatorPairFamilyFraction c h A B hA hB)))
    (hdetne : polynomialPairDet u v ≠ 0)
    (hdetdegree : (polynomialPairDet u v).natDegree < l) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_of_pair_span_det_with_span
      A B hA hB hbounded hcoeff hlD u v hu hv hdetne hdetdegree
  exact ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff⟩

end ProximityPrize.SubmissionLower

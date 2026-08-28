import ProximityPrize.SubmissionLower.BCHKSLocatorRankDropSelection6400

/-!
# Bounded locator obstruction from a polynomial rank drop

This module composes the abstract rank-drop selection with the coordinate
minor and Cramer accounting layers.  A strict loss of rank under the high
coefficient map produces a nonzero low-outer-degree polynomial obstruction;
if the high rank is at most `qMax`, its challenge coefficient degree is
bounded by `(q+1)S` for some `q <= qMax`.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {F : Type} [Field F]

noncomputable def locatorFractionDegreeLT
    (D : ℕ) (P : F[X][X]) (hP : P ∈ Polynomial.degreeLT F[X] D) :
    Polynomial.degreeLT (FractionRing F[X]) D :=
  ⟨P.map (algebraMap F[X] (FractionRing F[X])),
    Polynomial.mem_degreeLT.mpr
      (Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.mp hP))⟩

noncomputable def locatorFractionHighPart
    (D l : ℕ) :
    Polynomial.degreeLT (FractionRing F[X]) D →ₗ[FractionRing F[X]]
      (Fin (D - l) → FractionRing F[X]) :=
  (polynomialHighCoeffMap l (D - l)).comp
    (Polynomial.degreeLT (FractionRing F[X]) D).subtype

@[simp]
theorem locatorFractionHighPart_apply
    (D l : ℕ) (P : F[X][X])
    (hP : P ∈ Polynomial.degreeLT F[X] D) (t : Fin (D - l)) :
    locatorFractionHighPart D l (locatorFractionDegreeLT D P hP) t =
      algebraMap F[X] (FractionRing F[X]) (P.coeff (l + t.1)) := by
  simp [locatorFractionHighPart, locatorFractionDegreeLT,
    polynomialHighCoeffMap]

theorem exists_bounded_locatorCramerObstruction_of_rankDrop_with_span
    {I : Type} [Fintype I]
    {D l S qMax : ℕ} (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ i n, ((candidate i).coeff n).natDegree ≤ S)
    (hrank : Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (locatorFractionHighPart D l ∘
            (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) <
      Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)))))
    (hhighRank : Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (locatorFractionHighPart D l ∘
            (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) ≤ qMax) :
    ∃ q ≤ qMax, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X] (Set.range candidate) := by
  classical
  let K := FractionRing F[X]
  let full : I → Polynomial.degreeLT K D :=
    fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)
  let H : Polynomial.degreeLT K D →ₗ[K] (Fin (D - l) → K) :=
    locatorFractionHighPart D l
  obtain ⟨q, idx, hqrank, hfullLI, hhighLI, hlastSpan⟩ :=
    exists_fullIndependent_highBasis_with_extra full H (by
      simpa [K, full, H] using hrank)
  have hqmax : q ≤ qMax := by
    rw [hqrank]
    simpa [K, full, H] using hhighRank
  let g : Fin (q + 1) → F[X][X] := fun j => candidate (idx j)
  have hgLI : LinearIndependent F[X] g := by
    have hsubtype : LinearIndependent K
        (fun j : Fin (q + 1) => (full (idx j)).1) := by
      have hmap := hfullLI.map'
        (Polynomial.degreeLT K D).subtype
        (Polynomial.degreeLT K D).ker_subtype
      simpa [Function.comp_def] using hmap
    have hrestricted : LinearIndependent F[X]
        (fun j : Fin (q + 1) => (full (idx j)).1) :=
      hsubtype.restrict_scalars' F[X]
    let mapLinear : F[X][X] →ₗ[F[X]] K[X] :=
      (Polynomial.mapAlgHom (Algebra.ofId F[X] K)).toLinearMap
    apply LinearIndependent.of_comp mapLinear
    simpa [mapLinear, full, g, K, locatorFractionDegreeLT,
      Function.comp_def] using hrestricted
  have hhighLI' : LinearIndependent K
      (fun j : Fin q => fun t : Fin (D - l) =>
        algebraMap F[X] K ((g j.castSucc).coeff (l + t.1))) := by
    have heq : (fun j : Fin q => fun t : Fin (D - l) =>
        algebraMap F[X] K ((g j.castSucc).coeff (l + t.1))) =
        (fun j : Fin q => H (full (idx j.castSucc))) := by
      funext j t
      simp [K, full, H, g, locatorFractionHighPart_apply]
    rw [heq]
    exact hhighLI
  have hlastSpan' : (fun t : Fin (D - l) =>
      algebraMap F[X] K ((g (Fin.last q)).coeff (l + t.1))) ∈
      Submodule.span K (Set.range
        (fun j : Fin q => fun t : Fin (D - l) =>
          algebraMap F[X] K ((g j.castSucc).coeff (l + t.1)))) := by
    have hfirst : (fun j : Fin q => fun t : Fin (D - l) =>
        algebraMap F[X] K ((g j.castSucc).coeff (l + t.1))) =
        (fun j : Fin q => H (full (idx j.castSucc))) := by
      funext j t
      simp [K, full, H, g, locatorFractionHighPart_apply]
    have hlast : (fun t : Fin (D - l) =>
        algebraMap F[X] K ((g (Fin.last q)).coeff (l + t.1))) =
        H (full (idx (Fin.last q))) := by
      funext t
      simp [K, full, H, g, locatorFractionHighPart_apply]
    rw [hfirst, hlast]
    exact hlastSpan
  obtain ⟨Δ, hΔne, hΔdegree, hΔcoeff, hΔspan⟩ :=
    exists_bounded_locatorCramerObstruction_of_fraction_span_with_span g hgLI
      hhighLI' hlastSpan' (fun j => hbounded (idx j))
      (fun j n => hcoeff (idx j) n)
  have hspan_le : Submodule.span F[X] (Set.range g) ≤
      Submodule.span F[X] (Set.range candidate) := by
    rw [Submodule.span_le]
    intro P hP
    rcases hP with ⟨j, rfl⟩
    exact Submodule.subset_span ⟨idx j, rfl⟩
  exact ⟨q, hqmax, Δ, hΔne, hΔdegree, hΔcoeff, hspan_le hΔspan⟩

/-- Compatibility wrapper for callers which only use the obstruction's
degree bounds. -/
theorem exists_bounded_locatorCramerObstruction_of_rankDrop
    {I : Type} [Fintype I]
    {D l S qMax : ℕ} (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ i n, ((candidate i).coeff n).natDegree ≤ S)
    (hrank : Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (locatorFractionHighPart D l ∘
            (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) <
      Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)))))
    (hhighRank : Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (locatorFractionHighPart D l ∘
            (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) ≤ qMax) :
    ∃ q ≤ qMax, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_of_rankDrop_with_span
      candidate hbounded hcoeff hrank hhighRank
  exact ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff⟩

end ProximityPrize.SubmissionLower

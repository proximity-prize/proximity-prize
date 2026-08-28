import ProximityPrize.SubmissionLower.BCHKSLocatorRankDropObstruction6400

/-!
# Locator rank drop from one low candidate

A nonzero candidate already below the high-coefficient cutoff lies in the
kernel of the high-part map.  Selecting a basis of the full candidate span
shows that its high images are dependent, hence the high span has strictly
smaller rank.  Composing with the rank-drop Cramer pipeline produces the
bounded obstruction without a separate global determinant-rank theorem.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

variable {F : Type} [Field F]

theorem locatorFraction_rankDrop_of_low_candidate
    {I : Type} [Fintype I] {D l : ℕ}
    (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (i₀ : I) (hne : candidate i₀ ≠ 0)
    (hdegree : (candidate i₀).natDegree < l) :
    Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (locatorFractionHighPart D l ∘
            (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) <
      Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)))) := by
  classical
  let K := FractionRing F[X]
  letI : Field K := IsFractionRing.toField F[X]
  let full : I → Polynomial.degreeLT K D :=
    fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)
  let H : Polynomial.degreeLT K D →ₗ[K] (Fin (D - l) → K) :=
    locatorFractionHighPart D l
  have hxne : full i₀ ≠ 0 := by
    intro hx
    apply hne
    apply Polynomial.map_injective (algebraMap F[X] K)
      (IsFractionRing.injective F[X] K)
    have hxval := congrArg
      (fun y : Polynomial.degreeLT K D => (y.1 : K[X])) hx
    simpa [full, locatorFractionDegreeLT, K] using hxval
  have hxhigh : H (full i₀) = 0 := by
    change locatorFractionHighPart D l
      (locatorFractionDegreeLT D (candidate i₀) (hbounded i₀)) = 0
    funext t
    rw [locatorFractionHighPart_apply]
    change algebraMap F[X] K ((candidate i₀).coeff (l + t.1)) = 0
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have hrank := finrank_highSpan_lt_fullSpan_of_nonzero_mem_ker
    full H (full i₀)
      (Submodule.subset_span (Set.mem_range_self i₀)) hxne hxhigh
  simpa [K, full, H] using hrank

/-- More general interface: any nonzero fraction-field polynomial in the
candidate span which the high map kills forces the same strict rank drop. -/
theorem locatorFraction_rankDrop_of_span_kernel
    {I : Type} [Fintype I] {D l : ℕ}
    (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (w : Polynomial.degreeLT (FractionRing F[X]) D)
    (hwspan : w ∈ Submodule.span (FractionRing F[X]) (Set.range
      (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))
    (hwne : w ≠ 0) (hwker : locatorFractionHighPart D l w = 0) :
    Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (locatorFractionHighPart D l ∘
            (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) <
      Module.finrank (FractionRing F[X])
        (Submodule.span (FractionRing F[X]) (Set.range
          (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)))) := by
  let K := FractionRing F[X]
  letI : Field K := IsFractionRing.toField F[X]
  let full : I → Polynomial.degreeLT K D :=
    fun i => locatorFractionDegreeLT D (candidate i) (hbounded i)
  let H : Polynomial.degreeLT K D →ₗ[K] (Fin (D - l) → K) :=
    locatorFractionHighPart D l
  have hrank := finrank_highSpan_lt_fullSpan_of_nonzero_mem_ker
    full H w hwspan hwne hwker
  simpa [K, full, H] using hrank

/-- A nonzero low element of the fraction-field candidate span is enough for
the complete bounded obstruction; it need not be one original candidate. -/
theorem exists_bounded_locatorCramerObstruction_of_span_kernel_with_span
    {I : Type} [Fintype I]
    {D l S : ℕ} (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ i n, ((candidate i).coeff n).natDegree ≤ S)
    (w : Polynomial.degreeLT (FractionRing F[X]) D)
    (hwspan : w ∈ Submodule.span (FractionRing F[X]) (Set.range
      (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))
    (hwne : w ≠ 0) (hwker : locatorFractionHighPart D l w = 0) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X] (Set.range candidate) := by
  have hrank := locatorFraction_rankDrop_of_span_kernel
    candidate hbounded w hwspan hwne hwker
  have hhighRank : Module.finrank (FractionRing F[X])
      (Submodule.span (FractionRing F[X]) (Set.range
        (locatorFractionHighPart D l ∘
          (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) ≤
      D - l := by
    calc
      _ ≤ Module.finrank (FractionRing F[X])
          (Fin (D - l) → FractionRing F[X]) := Submodule.finrank_le _
      _ = D - l := by simp
  exact exists_bounded_locatorCramerObstruction_of_rankDrop_with_span
    candidate hbounded hcoeff hrank hhighRank

/-- Compatibility wrapper for the fraction-span low-element interface. -/
theorem exists_bounded_locatorCramerObstruction_of_span_kernel
    {I : Type} [Fintype I]
    {D l S : ℕ} (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ i n, ((candidate i).coeff n).natDegree ≤ S)
    (w : Polynomial.degreeLT (FractionRing F[X]) D)
    (hwspan : w ∈ Submodule.span (FractionRing F[X]) (Set.range
      (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))
    (hwne : w ≠ 0) (hwker : locatorFractionHighPart D l w = 0) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_of_span_kernel_with_span
      candidate hbounded hcoeff w hwspan hwne hwker
  exact ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff⟩

theorem exists_bounded_locatorCramerObstruction_of_low_candidate_with_span
    {I : Type} [Fintype I]
    {D l S : ℕ} (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ i n, ((candidate i).coeff n).natDegree ≤ S)
    (i₀ : I) (hne : candidate i₀ ≠ 0)
    (hdegree : (candidate i₀).natDegree < l) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X] (Set.range candidate) := by
  have hrank := locatorFraction_rankDrop_of_low_candidate
    candidate hbounded i₀ hne hdegree
  have hhighRank : Module.finrank (FractionRing F[X])
      (Submodule.span (FractionRing F[X]) (Set.range
        (locatorFractionHighPart D l ∘
          (fun i => locatorFractionDegreeLT D (candidate i) (hbounded i))))) ≤
      D - l := by
    calc
      _ ≤ Module.finrank (FractionRing F[X])
          (Fin (D - l) → FractionRing F[X]) := Submodule.finrank_le _
      _ = D - l := by simp
  exact exists_bounded_locatorCramerObstruction_of_rankDrop_with_span
    candidate hbounded hcoeff hrank hhighRank

/-- Compatibility wrapper for a distinguished low original candidate. -/
theorem exists_bounded_locatorCramerObstruction_of_low_candidate
    {I : Type} [Fintype I]
    {D l S : ℕ} (candidate : I → F[X][X])
    (hbounded : ∀ i, candidate i ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ i n, ((candidate i).coeff n).natDegree ≤ S)
    (i₀ : I) (hne : candidate i₀ ≠ 0)
    (hdegree : (candidate i₀).natDegree < l) :
    ∃ q ≤ D - l, ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_of_low_candidate_with_span
      candidate hbounded hcoeff i₀ hne hdegree
  exact ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff⟩

end ProximityPrize.SubmissionLower

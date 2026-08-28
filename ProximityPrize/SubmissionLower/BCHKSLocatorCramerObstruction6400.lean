import ProximityPrize.SubmissionLower.BCHKSLocatorKernelBasisBudget6400

/-!
# Bounded Cramer obstruction for the locator kernel

This module isolates the polynomial accounting in the large-nullity route.
Take `q + 1` bivariate polynomials which are linearly independent over the
challenge-polynomial ring.  Suppose the high `X`-coefficient vector of the
last polynomial lies in the span of the first `q`, and a selected `q`-square
coefficient minor is nonzero.  Cramer's rule clears the rational coefficients
without an uncontrolled denominator.

If every challenge coefficient of every input has degree at most `S`, the
resulting nonzero obstruction has challenge degree at most `(q + 1) * S`.
Only `q <= 9` is needed at score 64, so eleven retained kernel vectors cost
at most ten coarse kernel-basis budgets.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {F : Type} [Field F]

/-- A square polynomial matrix with entry degree at most `S` has determinant
degree at most its size times `S`. -/
theorem polynomialMatrix_det_natDegree_le_card_mul
    {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (S : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ S) :
    M.det.natDegree ≤ Fintype.card I * S := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc
    (∑ i : I, (M (σ i) i).natDegree) ≤ ∑ _i : I, S := by
      exact Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = Fintype.card I * S := by simp

/-- Each Cramer numerator obeys the same determinant bound as the original
matrix when the replacement column has the same entry cap. -/
theorem polynomialMatrix_cramer_natDegree_le_card_mul
    {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (b : I → F[X]) (S : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ S)
    (hb : ∀ i, (b i).natDegree ≤ S) (j : I) :
    (Matrix.cramer M b j).natDegree ≤ Fintype.card I * S := by
  rw [Matrix.cramer_apply]
  apply polynomialMatrix_det_natDegree_le_card_mul
  intro i k
  by_cases hkj : k = j
  · subst hkj
    simpa using hb i
  · simpa [Matrix.updateCol_apply, hkj] using hM i k

/-- The selected high-coefficient minor of the first `q` generators. -/
noncomputable def locatorCramerHighMatrix
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l)) : Matrix (Fin q) (Fin q) F[X] :=
  fun i j => (g j.castSucc).coeff (l + (rows i).1)

/-- The same selected high coefficients of the final generator. -/
noncomputable def locatorCramerHighTarget
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l)) : Fin q → F[X] :=
  fun i => (g (Fin.last q)).coeff (l + (rows i).1)

/-- Cramer coefficients: the last generator receives the selected minor;
the first `q` generators receive the negatives of the Cramer numerators. -/
noncomputable def locatorCramerCoefficients
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l)) : Fin (q + 1) → F[X] :=
  Fin.lastCases
    (locatorCramerHighMatrix g rows).det
    (fun j => -Matrix.cramer (locatorCramerHighMatrix g rows)
      (locatorCramerHighTarget g rows) j)

/-- The cleared low-`X`-degree obstruction. -/
noncomputable def locatorCramerObstruction
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l)) : F[X][X] :=
  ∑ j, locatorCramerCoefficients g rows j • g j

/-- Linear independence of the selected full polynomials prevents the
Cramer obstruction from disappearing when the selected minor is nonzero. -/
theorem locatorCramerObstruction_ne_zero
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l))
    (hindependent : LinearIndependent F[X] g)
    (hminor : (locatorCramerHighMatrix g rows).det ≠ 0) :
    locatorCramerObstruction g rows ≠ 0 := by
  intro hzero
  have hall := Fintype.linearIndependent_iff.mp hindependent
    (locatorCramerCoefficients g rows) hzero
  have hlast := hall (Fin.last q)
  have hlast' : (locatorCramerHighMatrix g rows).det = 0 := by
    simpa [locatorCramerCoefficients] using hlast
  exact hminor hlast'

/-- If the Cramer identity holds on every high coefficient, the obstruction
has outer degree below `l`.  Coefficients at or above the ambient cap `D`
vanish directly. -/
theorem locatorCramerObstruction_mem_degreeLT
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l))
    (hbounded : ∀ j, g j ∈ Polynomial.degreeLT F[X] D)
    (hidentity : ∀ t : Fin (D - l),
      (locatorCramerHighMatrix g rows).det *
          (g (Fin.last q)).coeff (l + t.1) =
        ∑ j : Fin q,
          Matrix.cramer (locatorCramerHighMatrix g rows)
              (locatorCramerHighTarget g rows) j *
            (g j.castSucc).coeff (l + t.1)) :
    locatorCramerObstruction g rows ∈ Polynomial.degreeLT F[X] l := by
  apply Polynomial.mem_degreeLT.mpr
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hln
  by_cases hnD : n < D
  · let t : Fin (D - l) := ⟨n - l, by omega⟩
    have ht : l + t.1 = n := by
      dsimp only [t]
      omega
    have hid := hidentity t
    rw [ht] at hid
    rw [show (locatorCramerObstruction g rows).coeff n =
        ∑ j : Fin (q + 1), locatorCramerCoefficients g rows j *
          (g j).coeff n by simp [locatorCramerObstruction]]
    rw [Fin.sum_univ_castSucc]
    simp only [locatorCramerCoefficients, Fin.lastCases_castSucc,
      Fin.lastCases_last, neg_mul]
    rw [hid]
    simp
  · have hDn : D ≤ n := Nat.le_of_not_gt hnD
    have hgzero : ∀ j, (g j).coeff n = 0 := by
      intro j
      exact Polynomial.coeff_eq_zero_of_degree_lt
        ((Polynomial.mem_degreeLT.mp (hbounded j)).trans_le
          (WithBot.coe_le_coe.mpr hDn))
    simp [locatorCramerObstruction, hgzero]

/-- Every Cramer coefficient has challenge degree at most `q*S`. -/
theorem locatorCramerCoefficients_natDegree_le
    {q D l S : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l))
    (hcoeff : ∀ j n, ((g j).coeff n).natDegree ≤ S)
    (j : Fin (q + 1)) :
    (locatorCramerCoefficients g rows j).natDegree ≤ q * S := by
  let A := locatorCramerHighMatrix g rows
  let b := locatorCramerHighTarget g rows
  have hA : ∀ i k, (A i k).natDegree ≤ S := by
    intro i k
    exact hcoeff k.castSucc (l + (rows i).1)
  have hb : ∀ i, (b i).natDegree ≤ S := by
    intro i
    exact hcoeff (Fin.last q) (l + (rows i).1)
  cases j using Fin.lastCases with
  | last =>
      simpa [locatorCramerCoefficients, A] using
        polynomialMatrix_det_natDegree_le_card_mul A S hA
  | cast j =>
      simpa [locatorCramerCoefficients, A, b] using
        polynomialMatrix_cramer_natDegree_le_card_mul A b S hA hb j

/-- The challenge degree of every outer coefficient of the obstruction is at
most `(q+1)S`: `qS` for a Cramer numerator and `S` for its generator. -/
theorem locatorCramerObstruction_coeff_natDegree_le
    {q D l S : ℕ} (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l))
    (hcoeff : ∀ j n, ((g j).coeff n).natDegree ≤ S)
    (n : ℕ) :
    ((locatorCramerObstruction g rows).coeff n).natDegree ≤
      (q + 1) * S := by
  rw [show (locatorCramerObstruction g rows).coeff n =
      ∑ j : Fin (q + 1), locatorCramerCoefficients g rows j *
        (g j).coeff n by simp [locatorCramerObstruction]]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  calc
    (locatorCramerCoefficients g rows j * (g j).coeff n).natDegree ≤
        (locatorCramerCoefficients g rows j).natDegree +
          ((g j).coeff n).natDegree := Polynomial.natDegree_mul_le
    _ ≤ q * S + S := Nat.add_le_add
      (locatorCramerCoefficients_natDegree_le g rows hcoeff j)
      (hcoeff j n)
    _ = (q + 1) * S := by ring

/-- Consolidated bounded Cramer extraction once the independent generators,
minor, and all-high-coefficient identity have been supplied. -/
theorem exists_bounded_locatorCramerObstruction_with_span
    {q D l S : ℕ}
    (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l))
    (hindependent : LinearIndependent F[X] g)
    (hminor : (locatorCramerHighMatrix g rows).det ≠ 0)
    (hbounded : ∀ j, g j ∈ Polynomial.degreeLT F[X] D)
    (hidentity : ∀ t : Fin (D - l),
      (locatorCramerHighMatrix g rows).det *
          (g (Fin.last q)).coeff (l + t.1) =
        ∑ j : Fin q,
          Matrix.cramer (locatorCramerHighMatrix g rows)
              (locatorCramerHighTarget g rows) j *
            (g j.castSucc).coeff (l + t.1))
    (hcoeff : ∀ j n, ((g j).coeff n).natDegree ≤ S) :
    ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X] (Set.range g) := by
  classical
  let Δ := locatorCramerObstruction g rows
  have hΔne : Δ ≠ 0 := locatorCramerObstruction_ne_zero
    g rows hindependent hminor
  have hΔmem : Δ ∈ Polynomial.degreeLT F[X] l :=
    locatorCramerObstruction_mem_degreeLT g rows hbounded hidentity
  refine ⟨Δ, hΔne, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_lt_iff_degree_lt hΔne]
    exact Polynomial.mem_degreeLT.mp hΔmem
  · intro n
    exact locatorCramerObstruction_coeff_natDegree_le g rows hcoeff n
  · dsimp only [Δ, locatorCramerObstruction]
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))

/-- Compatibility wrapper retaining the original bounded-obstruction
interface when span membership is not needed downstream. -/
theorem exists_bounded_locatorCramerObstruction
    {q D l S : ℕ}
    (g : Fin (q + 1) → F[X][X])
    (rows : Fin q → Fin (D - l))
    (hindependent : LinearIndependent F[X] g)
    (hminor : (locatorCramerHighMatrix g rows).det ≠ 0)
    (hbounded : ∀ j, g j ∈ Polynomial.degreeLT F[X] D)
    (hidentity : ∀ t : Fin (D - l),
      (locatorCramerHighMatrix g rows).det *
          (g (Fin.last q)).coeff (l + t.1) =
        ∑ j : Fin q,
          Matrix.cramer (locatorCramerHighMatrix g rows)
              (locatorCramerHighTarget g rows) j *
            (g j.castSucc).coeff (l + t.1))
    (hcoeff : ∀ j n, ((g j).coeff n).natDegree ≤ S) :
    ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_with_span g rows hindependent
      hminor hbounded hidentity hcoeff
  exact ⟨Δ, hΔne, hΔdegree, hΔcoeff⟩

end ProximityPrize.SubmissionLower

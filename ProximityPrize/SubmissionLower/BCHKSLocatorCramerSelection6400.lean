import ProximityPrize.SubmissionLower.BCHKSLocatorCramerObstruction6400

/-!
# Coordinate-minor and Cramer selection for the locator kernel

This module turns fraction-field independence of finitely many high
coefficient columns into a nonzero polynomial coordinate minor.  If the last
high column lies in their fraction-field span, the selected minor supplies
the all-row Cramer identity over the original polynomial ring.  Thus no
uncontrolled rational denominator enters the obstruction degree bound.
-/

namespace ProximityPrize.SubmissionLower

open Module Submodule
open Polynomial
open scoped Matrix

set_option autoImplicit false

variable {F : Type} [Field F]

theorem exists_coordinate_minor_ne_zero
    {q r : ℕ} (v : Fin q → (Fin r → F))
    (hv : LinearIndependent F v) :
    ∃ rows : Fin q → Fin r,
      (Matrix.of fun i j => v j (rows i)).det ≠ 0 := by
  classical
  let W : Submodule F (Fin r → F) := Submodule.span F (Set.range v)
  let inclusion : W →ₗ[F] (Fin r → F) := W.subtype
  letI : FiniteDimensional F W :=
    FiniteDimensional.of_injective inclusion W.injective_subtype
  let ambientDualBasis : Basis (Fin r) F (Module.Dual F (Fin r → F)) :=
    (Pi.basisFun F (Fin r)).dualBasis
  let coord : Fin r → Module.Dual F W :=
    fun i => inclusion.dualMap (ambientDualBasis i)
  have hcoordSpan : Submodule.span F (Set.range coord) = ⊤ := by
    have hsurj : Function.Surjective inclusion.dualMap :=
      LinearMap.dualMap_surjective_of_injective W.injective_subtype
    change Submodule.span F
      (Set.range (inclusion.dualMap ∘ ambientDualBasis)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, ambientDualBasis.span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  haveI : Module.Finite F
      (Submodule.span F (Set.range coord)) := by
    rw [hcoordSpan]
    infer_instance
  obtain ⟨f, hfcoord, hfspan, hfindependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range coord)
  have hWrank : Module.finrank F W = q := by
    simpa [W] using finrank_span_eq_card hv
  have hdualrank : Module.finrank F (Module.Dual F W) = q := by
    rw [Subspace.dual_finrank_eq, hWrank]
  have hselectedRank :
      Module.finrank F (Submodule.span F (Set.range coord)) = q := by
    rw [hcoordSpan, finrank_top, hdualrank]
  let e : Fin q ≃
      Fin (Module.finrank F (Submodule.span F (Set.range coord))) :=
    finCongr hselectedRank.symm
  have hexistsRows : ∀ i : Fin q, ∃ row : Fin r, coord row = f (e i) := by
    intro i
    exact hfcoord (e i)
  choose rows hrows using hexistsRows
  let A : Matrix (Fin q) (Fin q) F := Matrix.of fun i j => v j (rows i)
  have hAzero : ∀ c : Fin q → F, A *ᵥ c = 0 → c = 0 := by
    intro c hc
    let x : W := ⟨∑ j, c j • v j, by
      apply Submodule.sum_mem
      intro j hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))⟩
    have hfzero : ∀ k, f k x = 0 := by
      intro k
      let i : Fin q := e.symm k
      have hrow := congrFun hc i
      have hselected : coord (rows i) = f (e i) := hrows i
      have heik : e i = k := e.apply_symm_apply k
      rw [heik] at hselected
      rw [← hselected]
      simpa [coord, inclusion, ambientDualBasis, x, A, Matrix.mulVec,
        dotProduct, mul_comm] using hrow
    have hdualzero : ∀ φ : Module.Dual F W, φ x = 0 := by
      intro φ
      have hmem : φ ∈ Submodule.span F (Set.range f) := by
        rw [hfspan, hcoordSpan]
        exact Submodule.mem_top
      refine Submodule.span_induction (p := fun ψ _ => ψ x = 0)
        ?_ ?_ ?_ ?_ hmem
      · intro ψ hψ
        rcases hψ with ⟨k, rfl⟩
        exact hfzero k
      · simp
      · intro ψ χ hψ hχ hψzero hχzero
        simp [hψzero, hχzero]
      · intro a ψ hψ hψzero
        simp [hψzero]
    have hxzero : x = 0 :=
      (Module.forall_dual_apply_eq_zero_iff F x).mp hdualzero
    have hsum : ∑ j, c j • v j = 0 := by
      exact congrArg Subtype.val hxzero
    have hczero := Fintype.linearIndependent_iff.mp hv c hsum
    exact funext hczero
  have hAinjective : Function.Injective A.mulVec := by
    intro c d hcd
    apply sub_eq_zero.mp
    apply hAzero (c - d)
    simpa [Matrix.mulVec_sub] using congrArg (fun z => z - A *ᵥ d) hcd
  have hAunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hAinjective
  exact ⟨rows, ((Matrix.isUnit_iff_isUnit_det A).mp hAunit).ne_zero⟩

theorem map_matrix_cramer
    {R K I : Type} [CommRing R] [CommRing K]
    [Fintype I] [DecidableEq I]
    (f : R →+* K) (A : Matrix I I R) (b : I → R) (j : I) :
    f (Matrix.cramer A b j) =
      Matrix.cramer (A.map f) (fun i => f (b i)) j := by
  simp only [Matrix.cramer_apply, f.map_det]
  congr 1
  ext i k
  by_cases h : k = j <;> simp [h]

theorem exists_locatorCramer_rows_of_fraction_span
    {q D l : ℕ} (g : Fin (q + 1) → F[X][X])
    (hindependentHigh : LinearIndependent (FractionRing F[X])
      (fun j : Fin q => fun t : Fin (D - l) =>
        algebraMap F[X] (FractionRing F[X])
          ((g j.castSucc).coeff (l + t.1))))
    (hlastSpan : (fun t : Fin (D - l) =>
        algebraMap F[X] (FractionRing F[X])
          ((g (Fin.last q)).coeff (l + t.1))) ∈
      Submodule.span (FractionRing F[X]) (Set.range
        (fun j : Fin q => fun t : Fin (D - l) =>
          algebraMap F[X] (FractionRing F[X])
            ((g j.castSucc).coeff (l + t.1))))) :
    ∃ rows : Fin q → Fin (D - l),
      (locatorCramerHighMatrix g rows).det ≠ 0 ∧
      ∀ t : Fin (D - l),
        (locatorCramerHighMatrix g rows).det *
            (g (Fin.last q)).coeff (l + t.1) =
          ∑ j : Fin q,
            Matrix.cramer (locatorCramerHighMatrix g rows)
                (locatorCramerHighTarget g rows) j *
              (g j.castSucc).coeff (l + t.1) := by
  classical
  let R := F[X]
  let K := FractionRing R
  let ι : R →+* K := algebraMap R K
  let vR : Fin q → Fin (D - l) → R :=
    fun j t => (g j.castSucc).coeff (l + t.1)
  let bR : Fin (D - l) → R :=
    fun t => (g (Fin.last q)).coeff (l + t.1)
  let vK : Fin q → Fin (D - l) → K :=
    fun j t => ι (vR j t)
  let bK : Fin (D - l) → K := fun t => ι (bR t)
  have hvK : LinearIndependent K vK := by
    simpa [R, K, ι, vR, vK] using hindependentHigh
  have hbKspan : bK ∈ Submodule.span K (Set.range vK) := by
    simpa [R, K, ι, vR, bR, vK, bK] using hlastSpan
  obtain ⟨rows, hminorK⟩ := exists_coordinate_minor_ne_zero vK hvK
  let AR : Matrix (Fin q) (Fin q) R :=
    Matrix.of fun i j => vR j (rows i)
  let aR : Fin q → R := fun i => bR (rows i)
  let AK : Matrix (Fin q) (Fin q) K :=
    Matrix.of fun i j => vK j (rows i)
  let aK : Fin q → K := fun i => bK (rows i)
  have hminorK' : AK.det ≠ 0 := by
    simpa [AK] using hminorK
  have hminorR : AR.det ≠ 0 := by
    intro hzero
    apply hminorK'
    have hmap : ι AR.det = AK.det := by
      rw [ι.map_det]
      rfl
    rw [← hmap, hzero, map_zero]
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp hbKspan
  have hselected : AK *ᵥ c = aK := by
    funext i
    have hi := congrFun hc (rows i)
    simpa [AK, aK, vK, bK, Matrix.mulVec, dotProduct,
      mul_comm] using hi
  have hAKunit : IsUnit AK :=
    (Matrix.isUnit_iff_isUnit_det AK).mpr (isUnit_iff_ne_zero.mpr hminorK')
  have hAKinjective : Function.Injective AK.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hAKunit
  have hcramer : Matrix.cramer AK aK = AK.det • c := by
    apply hAKinjective
    rw [Matrix.mulVec_cramer]
    simpa [hselected] using (Matrix.mulVec_smul AK AK.det c).symm
  have hidentityK : ∀ t : Fin (D - l),
      AK.det * bK t =
        ∑ j : Fin q, Matrix.cramer AK aK j * vK j t := by
    intro t
    have ht := congrFun hc t
    rw [hcramer]
    simp only [Pi.smul_apply, smul_eq_mul]
    have ht' : ∑ j : Fin q, c j * vK j t = bK t := by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ht
    rw [← ht', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  refine ⟨rows, ?_, ?_⟩
  · change AR.det ≠ 0
    exact hminorR
  · intro t
    apply IsFractionRing.injective R K
    have ht := hidentityK t
    simp only [map_mul, map_sum, map_matrix_cramer]
    rw [ι.map_det]
    change AK.det * bK t =
      ∑ j : Fin q, Matrix.cramer AK aK j * vK j t
    exact ht

/-- Fraction-field independence and span are sufficient for the complete
bounded obstruction package.  The coordinate rows, nonzero minor, and
all-high Cramer identity are constructed internally. -/
theorem exists_bounded_locatorCramerObstruction_of_fraction_span_with_span
    {q D l S : ℕ} (g : Fin (q + 1) → F[X][X])
    (hindependent : LinearIndependent F[X] g)
    (hindependentHigh : LinearIndependent (FractionRing F[X])
      (fun j : Fin q => fun t : Fin (D - l) =>
        algebraMap F[X] (FractionRing F[X])
          ((g j.castSucc).coeff (l + t.1))))
    (hlastSpan : (fun t : Fin (D - l) =>
        algebraMap F[X] (FractionRing F[X])
          ((g (Fin.last q)).coeff (l + t.1))) ∈
      Submodule.span (FractionRing F[X]) (Set.range
        (fun j : Fin q => fun t : Fin (D - l) =>
          algebraMap F[X] (FractionRing F[X])
            ((g j.castSucc).coeff (l + t.1)))))
    (hbounded : ∀ j, g j ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ j n, ((g j).coeff n).natDegree ≤ S) :
    ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S) ∧
      Δ ∈ Submodule.span F[X] (Set.range g) := by
  obtain ⟨rows, hminor, hidentity⟩ :=
    exists_locatorCramer_rows_of_fraction_span g
      hindependentHigh hlastSpan
  exact exists_bounded_locatorCramerObstruction_with_span g rows hindependent
    hminor hbounded hidentity hcoeff

/-- Compatibility wrapper for callers which only use the degree bounds. -/
theorem exists_bounded_locatorCramerObstruction_of_fraction_span
    {q D l S : ℕ} (g : Fin (q + 1) → F[X][X])
    (hindependent : LinearIndependent F[X] g)
    (hindependentHigh : LinearIndependent (FractionRing F[X])
      (fun j : Fin q => fun t : Fin (D - l) =>
        algebraMap F[X] (FractionRing F[X])
          ((g j.castSucc).coeff (l + t.1))))
    (hlastSpan : (fun t : Fin (D - l) =>
        algebraMap F[X] (FractionRing F[X])
          ((g (Fin.last q)).coeff (l + t.1))) ∈
      Submodule.span (FractionRing F[X]) (Set.range
        (fun j : Fin q => fun t : Fin (D - l) =>
          algebraMap F[X] (FractionRing F[X])
            ((g j.castSucc).coeff (l + t.1)))))
    (hbounded : ∀ j, g j ∈ Polynomial.degreeLT F[X] D)
    (hcoeff : ∀ j n, ((g j).coeff n).natDegree ≤ S) :
    ∃ Δ : F[X][X], Δ ≠ 0 ∧ Δ.natDegree < l ∧
      ∀ n, (Δ.coeff n).natDegree ≤ (q + 1) * S := by
  obtain ⟨Δ, hΔne, hΔdegree, hΔcoeff, _⟩ :=
    exists_bounded_locatorCramerObstruction_of_fraction_span_with_span
      g hindependent hindependentHigh hlastSpan hbounded hcoeff
  exact ⟨Δ, hΔne, hΔdegree, hΔcoeff⟩

end ProximityPrize.SubmissionLower

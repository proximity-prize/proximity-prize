import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialCramerFamily6400
import ProximityPrize.SubmissionLower.BCHKSPolynomialPairRankTwoCramer6400

/-!
# Rank-two assembly from the explicit locator Cramer family

The polynomial Cramer vectors are converted into bounded bivariate multiplier
pairs.  This file proves that coefficientwise passage to the fraction field
commutes with that conversion, preserves linear independence, and charges at
most twice the coordinate challenge-degree cap to every pair determinant.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- Rational multiplier pairs whose coefficient coordinates lie in the
generic production-locator kernel. -/
noncomputable def score6400LocatorRationalPairKernel
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    Submodule (FractionRing IRSProfile.Field[X])
      (PolynomialPairSpace (FractionRing IRSProfile.Field[X])
        locatorOrdinaryRows6400 locatorFrobeniusRows6400) :=
  (LinearMap.ker
    ((score6400LocatorPolynomialMatrix f₀ f₁).map
      (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))).mulVecLin).comap
    (polynomialPairCoordinateEquiv
      (FractionRing IRSProfile.Field[X])
      locatorOrdinaryRows6400 locatorFrobeniusRows6400).toLinearMap

/-- Applying an inverse linear equivalence to an element of a generated span
puts it in the span of the inverse images of the generators. -/
theorem symm_mem_span_range_of_mem_span_range
    {K V W I : Type} [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (e : W ≃ₗ[K] V) (g : I → V) (x : V)
    (hx : x ∈ Submodule.span K (Set.range g)) :
    e.symm x ∈ Submodule.span K (Set.range (fun i ↦ e.symm (g i))) := by
  have hxmap : e.symm x ∈
      Submodule.map e.symm.toLinearMap
        (Submodule.span K (Set.range g)) := by
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Submodule.map_span] at hxmap
  have himage : ⇑e.symm.toLinearMap '' Set.range g =
      Set.range (fun i ↦ e.symm (g i)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, ⟨i, rfl⟩, rfl⟩
  rwa [himage] at hxmap

/-- Mapping the two polynomial multiplier blocks to the fraction field is the
same as first mapping every coordinate and then applying the coordinate-pair
equivalence there. -/
theorem score6400_locatorFractionRelationPair_eq_coordinatePair
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) :
    (locatorFractionDegreeLT locatorOrdinaryRows6400
        (score6400PolynomialLocatorRelationPair q).1.1
        (score6400PolynomialLocatorRelationPair q).1.2,
      locatorFractionDegreeLT locatorFrobeniusRows6400
        (score6400PolynomialLocatorRelationPair q).2.1
        (score6400PolynomialLocatorRelationPair q).2.2) =
      (polynomialPairCoordinateEquiv
        (FractionRing IRSProfile.Field[X])
        locatorOrdinaryRows6400 locatorFrobeniusRows6400).symm
          ((algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])) ∘ q) := by
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  apply e.injective
  rw [e.apply_symm_apply]
  funext i
  cases i with
  | inl i =>
      have hq := score6400PolynomialLocatorRelationPair_inl_coeff q i
      rw [degreeLTEquiv_apply_eq_coeff] at hq
      have hmapped := congrArg ι hq
      simpa only [e, K, ι, polynomialPairCoordinateEquiv,
        LinearEquiv.trans_apply, LinearEquiv.coe_coe,
        LinearEquiv.prodCongr_apply,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
        degreeLTEquiv_apply_eq_coeff, locatorFractionDegreeLT,
        Polynomial.coeff_map, Function.comp_apply] using hmapped
  | inr i =>
      have hq := score6400PolynomialLocatorRelationPair_inr_coeff q i
      rw [degreeLTEquiv_apply_eq_coeff] at hq
      have hmapped := congrArg ι hq
      simpa only [e, K, ι, polynomialPairCoordinateEquiv,
        LinearEquiv.trans_apply, LinearEquiv.coe_coe,
        LinearEquiv.prodCongr_apply,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr,
        degreeLTEquiv_apply_eq_coeff, locatorFractionDegreeLT,
        Polynomial.coeff_map, Function.comp_apply] using hmapped

/-- Coordinatewise fraction-field independence transfers to the corresponding
two polynomial multiplier blocks. -/
theorem linearIndependent_score6400_locatorFractionRelationPair
    {I : Type}
    (q : I → Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : LinearIndependent (FractionRing IRSProfile.Field[X])
      (fun i ↦ (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X])) ∘ q i)) :
    LinearIndependent (FractionRing IRSProfile.Field[X])
      (fun i ↦
        (locatorFractionDegreeLT locatorOrdinaryRows6400
            (score6400PolynomialLocatorRelationPair (q i)).1.1
            (score6400PolynomialLocatorRelationPair (q i)).1.2,
          locatorFractionDegreeLT locatorFrobeniusRows6400
            (score6400PolynomialLocatorRelationPair (q i)).2.1
            (score6400PolynomialLocatorRelationPair (q i)).2.2)) := by
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  let family : I →
      (Polynomial.degreeLT K locatorOrdinaryRows6400) ×
        (Polynomial.degreeLT K locatorFrobeniusRows6400) :=
    fun i ↦
      (locatorFractionDegreeLT locatorOrdinaryRows6400
          (score6400PolynomialLocatorRelationPair (q i)).1.1
          (score6400PolynomialLocatorRelationPair (q i)).1.2,
        locatorFractionDegreeLT locatorFrobeniusRows6400
          (score6400PolynomialLocatorRelationPair (q i)).2.1
          (score6400PolynomialLocatorRelationPair (q i)).2.2)
  change LinearIndependent K family
  apply LinearIndependent.of_comp e.toLinearMap
  have hfamily : (⇑e.toLinearMap ∘ family) =
      (fun i ↦ ι ∘ q i) := by
    funext i
    change e (family i) = ι ∘ q i
    rw [show family i = e.symm (ι ∘ q i) by
      simpa only [family, K, ι, e] using
        score6400_locatorFractionRelationPair_eq_coordinatePair (q i)]
    exact e.apply_symm_apply (ι ∘ q i)
  rw [hfamily]
  simpa only [K, ι] using hq

/-- If every coefficient of four bivariate multipliers has challenge degree
at most `S`, every coefficient of their alternating determinant has degree at
most `2*S`. -/
theorem locatorPairDetCandidate_coeff_natDegree_le_two_mul
    {F I : Type} [Field F] (A B : I → F[X][X]) (S : ℕ)
    (hA : ∀ i n, ((A i).coeff n).natDegree ≤ S)
    (hB : ∀ i n, ((B i).coeff n).natDegree ≤ S)
    (ij : I × I) (n : ℕ) :
    ((locatorPairDetCandidate A B ij).coeff n).natDegree ≤ 2 * S := by
  rw [locatorPairDetCandidate, Polynomial.coeff_sub]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · rw [Polynomial.coeff_mul]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro ab hab
    exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add (hA ij.1 ab.1) (hB ij.2 ab.2)).trans_eq
        (by omega))
  · rw [Polynomial.coeff_mul]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro ab hab
    exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add (hB ij.1 ab.1) (hA ij.2 ab.2)).trans_eq
        (by omega))

/-- Degree-`<c` and degree-`<h` multiplier blocks have pair determinants of
degree below `c+h-1`. -/
theorem locatorPairDetCandidate_mem_degreeLT_add_sub_one
    {F I : Type} [Field F] (c h : ℕ) (hc : 0 < c) (hh : 0 < h)
    (A B : I → F[X][X])
    (hA : ∀ i, A i ∈ Polynomial.degreeLT F[X] c)
    (hB : ∀ i, B i ∈ Polynomial.degreeLT F[X] h)
    (ij : I × I) :
    locatorPairDetCandidate A B ij ∈
      Polynomial.degreeLT F[X] (c + h - 1) := by
  have hAdegree : ∀ i, (A i).natDegree < c := by
    intro i
    by_cases hzero : A i = 0
    · simpa [hzero] using hc
    · rw [Polynomial.natDegree_lt_iff_degree_lt hzero]
      exact Polynomial.mem_degreeLT.mp (hA i)
  have hBdegree : ∀ i, (B i).natDegree < h := by
    intro i
    by_cases hzero : B i = 0
    · simpa [hzero] using hh
    · rw [Polynomial.natDegree_lt_iff_degree_lt hzero]
      exact Polynomial.mem_degreeLT.mp (hB i)
  let P := locatorPairDetCandidate A B ij
  have hPdegree : P.natDegree < c + h - 1 := by
    have hPform : P = A ij.1 * B ij.2 - B ij.1 * A ij.2 := rfl
    rw [hPform]
    calc
      (A ij.1 * B ij.2 - B ij.1 * A ij.2).natDegree ≤
          max (A ij.1 * B ij.2).natDegree
            (B ij.1 * A ij.2).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ max ((A ij.1).natDegree + (B ij.2).natDegree)
          ((B ij.1).natDegree + (A ij.2).natDegree) := by
        apply max_le
        · exact Polynomial.natDegree_mul_le.trans
            (Nat.le_max_left _ _)
        · exact Polynomial.natDegree_mul_le.trans
            (Nat.le_max_right _ _)
      _ < c + h - 1 := by
        exact max_lt
          (by have := hAdegree ij.1; have := hBdegree ij.2; omega)
          (by have := hBdegree ij.1; have := hAdegree ij.2; omega)
  by_cases hzero : P = 0
  · have hmem : P ∈ Polynomial.degreeLT F[X] (c + h - 1) := by
      rw [hzero]
      exact Submodule.zero_mem _
    simpa only [P] using hmem
  · have hmem : P ∈ Polynomial.degreeLT F[X] (c + h - 1) := by
      rw [Polynomial.mem_degreeLT,
        ← Polynomial.natDegree_lt_iff_degree_lt hzero]
      exact hPdegree
    simpa only [P] using hmem

/-- Evaluation after changing coefficients preserves every vanishing property
shared by the generators of a polynomial span. -/
theorem polynomial_map_eval_eq_zero_of_mem_span
    {R K I : Type} [CommRing R] [Field K]
    (φ : R →+* K) (x : K) (g : I → R[X]) (P : R[X])
    (hP : P ∈ Submodule.span R (Set.range g))
    (hg : ∀ i, ((g i).map φ).eval x = 0) :
    (P.map φ).eval x = 0 := by
  refine Submodule.span_induction
    (p := fun Q _ ↦ (Q.map φ).eval x = 0) ?_ ?_ ?_ ?_ hP
  · intro Q hQ
    rcases hQ with ⟨i, rfl⟩
    exact hg i
  · simp
  · intro Q S hQ hS hQzero hSzero
    simp [hQzero, hSzero]
  · intro a Q hQ hQzero
    simp [smul_eq_C_mul, hQzero]

/-- Challenge evaluation commutes with the raw alternating determinant of
two polynomial-valued locator relation pairs. -/
theorem score6400PolynomialLocatorRelationPair_det_map_eval
    (q₀ q₁ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (z : IRSProfile.Field) :
    (((score6400PolynomialLocatorRelationPair q₀).1.1 *
        (score6400PolynomialLocatorRelationPair q₁).2.1 -
      (score6400PolynomialLocatorRelationPair q₀).2.1 *
        (score6400PolynomialLocatorRelationPair q₁).1.1).map
          (Polynomial.evalRingHom z)) =
      polynomialPairDet
        (score6400LocatorRelationPair (fun n ↦ (q₀ n).eval z))
        (score6400LocatorRelationPair (fun n ↦ (q₁ n).eval z)) := by
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
    score6400PolynomialLocatorRelationPair_fst_map_eval,
    score6400PolynomialLocatorRelationPair_snd_map_eval,
    score6400PolynomialLocatorRelationPair_snd_map_eval,
    score6400PolynomialLocatorRelationPair_fst_map_eval]
  simp only [polynomialPairDet]

/-- One selected polynomial Cramer vector of the production locator matrix. -/
noncomputable def score6400SelectedLocatorCramerVector
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    Score6400LocatorMinorIndex → IRSProfile.Field[X] :=
  selectedPolynomialCramerKernelVector
    (score6400LocatorPolynomialMatrix f₀ f₁) rows cols hcols j

/-- Ordinary bivariate multiplier belonging to a selected Cramer vector. -/
noncomputable def score6400SelectedLocatorCramerOrdinary
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) : IRSProfile.Field[X][X] :=
  (score6400PolynomialLocatorRelationPair
    (score6400SelectedLocatorCramerVector
      f₀ f₁ rows cols hcols j)).1.1

/-- Frobenius bivariate multiplier belonging to a selected Cramer vector. -/
noncomputable def score6400SelectedLocatorCramerFrobenius
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) : IRSProfile.Field[X][X] :=
  (score6400PolynomialLocatorRelationPair
    (score6400SelectedLocatorCramerVector
      f₀ f₁ rows cols hcols j)).2.1

theorem score6400SelectedLocatorCramerOrdinary_mem_degreeLT
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    score6400SelectedLocatorCramerOrdinary f₀ f₁ rows cols hcols j ∈
      Polynomial.degreeLT IRSProfile.Field[X]
        locatorOrdinaryRows6400 :=
  (score6400PolynomialLocatorRelationPair
    (score6400SelectedLocatorCramerVector
      f₀ f₁ rows cols hcols j)).1.2

theorem score6400SelectedLocatorCramerFrobenius_mem_degreeLT
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    score6400SelectedLocatorCramerFrobenius f₀ f₁
        rows cols hcols j ∈
      Polynomial.degreeLT IRSProfile.Field[X]
        locatorFrobeniusRows6400 :=
  (score6400PolynomialLocatorRelationPair
    (score6400SelectedLocatorCramerVector
      f₀ f₁ rows cols hcols j)).2.2

/-- The selected bivariate Cramer pairs are independent over the challenge
fraction field whenever the selected minor is nonzero there. -/
theorem linearIndependent_score6400SelectedLocatorCramerFractionPairs
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (hdet : (algebraMap IRSProfile.Field[X]
      (FractionRing IRSProfile.Field[X]))
        (selectedPolynomialPivotBlock
          (score6400LocatorPolynomialMatrix f₀ f₁) rows cols).det ≠ 0) :
    LinearIndependent (FractionRing IRSProfile.Field[X])
      (locatorPairFamilyFraction
        locatorOrdinaryRows6400 locatorFrobeniusRows6400
        (score6400SelectedLocatorCramerOrdinary
          f₀ f₁ rows cols hcols)
        (score6400SelectedLocatorCramerFrobenius
          f₀ f₁ rows cols hcols)
        (score6400SelectedLocatorCramerOrdinary_mem_degreeLT
          f₀ f₁ rows cols hcols)
        (score6400SelectedLocatorCramerFrobenius_mem_degreeLT
          f₀ f₁ rows cols hcols)) := by
  apply linearIndependent_score6400_locatorFractionRelationPair
  exact linearIndependent_mappedSelectedPolynomialCramerKernelVector
    (algebraMap IRSProfile.Field[X]
      (FractionRing IRSProfile.Field[X]))
    (score6400LocatorPolynomialMatrix f₀ f₁)
    rows cols hcols hdet

/-- A pair determinant of selected Cramer vectors always has outer degree
strictly below `76780`. -/
theorem score6400SelectedLocatorPairDet_mem_degreeLT_76780
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (ij : SelectedColumnComplement cols ×
      SelectedColumnComplement cols) :
    locatorPairDetCandidate
        (score6400SelectedLocatorCramerOrdinary
          f₀ f₁ rows cols hcols)
        (score6400SelectedLocatorCramerFrobenius
          f₀ f₁ rows cols hcols) ij ∈
      Polynomial.degreeLT IRSProfile.Field[X] 76780 := by
  simpa only [locatorOrdinaryRows6400, locatorFrobeniusRows6400] using
    locatorPairDetCandidate_mem_degreeLT_add_sub_one
      locatorOrdinaryRows6400 locatorFrobeniusRows6400
      (by norm_num) (by norm_num)
      (score6400SelectedLocatorCramerOrdinary
        f₀ f₁ rows cols hcols)
      (score6400SelectedLocatorCramerFrobenius
        f₀ f₁ rows cols hcols)
      (score6400SelectedLocatorCramerOrdinary_mem_degreeLT
        f₀ f₁ rows cols hcols)
      (score6400SelectedLocatorCramerFrobenius_mem_degreeLT
        f₀ f₁ rows cols hcols) ij

/-- The coordinate bound on selected Cramer vectors gives the promised
twice-`r*p` coefficient cap on every pair determinant. -/
theorem score6400SelectedLocatorPairDet_coeff_natDegree_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (hdegree : ∀ (j : SelectedColumnComplement cols)
        (n : Score6400LocatorMinorIndex),
      (score6400SelectedLocatorCramerVector
        f₀ f₁ rows cols hcols j n).natDegree ≤ r * 2130706433)
    (ij : SelectedColumnComplement cols ×
      SelectedColumnComplement cols) (n : ℕ) :
    ((locatorPairDetCandidate
      (score6400SelectedLocatorCramerOrdinary
        f₀ f₁ rows cols hcols)
      (score6400SelectedLocatorCramerFrobenius
        f₀ f₁ rows cols hcols) ij).coeff n).natDegree ≤
      2 * (r * 2130706433) := by
  apply locatorPairDetCandidate_coeff_natDegree_le_two_mul
  · intro j k
    exact score6400PolynomialLocatorRelationPair_fst_coeff_natDegree_le
      (score6400SelectedLocatorCramerVector
        f₀ f₁ rows cols hcols j)
      (r * 2130706433) k (hdegree j)
  · intro j k
    exact score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
      (score6400SelectedLocatorCramerVector
        f₀ f₁ rows cols hcols j)
      (r * 2130706433) k (hdegree j)

/-- Specializing the challenge coefficients of a selected polynomial pair
determinant gives the determinant of the two specialized locator relations. -/
theorem score6400SelectedLocatorPairDet_map_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : ℕ}
    (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (ij : SelectedColumnComplement cols ×
      SelectedColumnComplement cols)
    (z : IRSProfile.Field) :
    (locatorPairDetCandidate
      (score6400SelectedLocatorCramerOrdinary
        f₀ f₁ rows cols hcols)
      (score6400SelectedLocatorCramerFrobenius
        f₀ f₁ rows cols hcols) ij).map
          (Polynomial.evalRingHom z) =
      polynomialPairDet
        (score6400LocatorRelationPair (fun n ↦
          (score6400SelectedLocatorCramerVector
            f₀ f₁ rows cols hcols ij.1 n).eval z))
        (score6400LocatorRelationPair (fun n ↦
          (score6400SelectedLocatorCramerVector
            f₀ f₁ rows cols hcols ij.2 n).eval z)) := by
  simpa only [locatorPairDetCandidate,
    score6400SelectedLocatorCramerOrdinary,
    score6400SelectedLocatorCramerFrobenius] using
      score6400PolynomialLocatorRelationPair_det_map_eval
        (score6400SelectedLocatorCramerVector
          f₀ f₁ rows cols hcols ij.1)
        (score6400SelectedLocatorCramerVector
          f₀ f₁ rows cols hcols ij.2) z

/-- Per-slope semantic data carried by a rooted polynomial Cramer
obstruction.  The agreement set is the original `MCABad` support, while the
error set is the full complement of the chosen decoding polynomial. -/
structure Score6400RootedCramerObstructionData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (Δ : IRSProfile.Field[X][X]) where
  agreementSet : Finset IRSProfile.Index
  polynomial : IRSProfile.Field[X]
  errorSet : Finset IRSProfile.Index
  agreementSet_large : 185364 ≤ agreementSet.card
  polynomial_degree : polynomial.natDegree ≤ 131071
  agreement : ∀ i ∈ agreementSet,
    polynomial.eval (IRSProfile.domain i) = f₀ i + z * f₁ i
  unexplainedPair : ¬BCHKSExactSparsification6400.ExplainedPair
    IRSProfile.baseCode f₀ f₁ agreementSet
  errorSet_eq : errorSet = Finset.univ.filter (fun i =>
    (f₀ i + z * f₁ i) -
      polynomial.eval (IRSProfile.domain i) ≠ 0)
  errorSet_large : 76771 ≤ errorSet.card
  errorSet_small : errorSet.card ≤ 76780
  obstruction_roots : ∀ i, i ∈ errorSet →
    (Δ.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) = 0

/-- Complete algebraic assembly of the generic-rank-two locator branch.
Starting only from the rational kernel dimension and a nonzero alternating
determinant inside the rational pair kernel, this theorem selects the
polynomial Cramer family and feeds it through the sharp rank-two/Cramer
pipeline. -/
theorem exists_score6400_bounded_obstruction_of_locatorPairKernel_rankTwo
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L l : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hL : L ≤ 76781) (hcut : 76781 - L < l) (hl : l ≤ 76780)
    (hrankTwo : ∃ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ r ≤ 76781, ∃ q ≤ 76780 - l, ∃ Δ : IRSProfile.Field[X][X],
      Δ ≠ 0 ∧ Δ.natDegree < l ∧
      (∀ n, (Δ.coeff n).natDegree ≤
        (q + 1) * (2 * (r * 2130706433))) ∧
      ∀ z : IRSProfile.Field,
        MCABad IRSProfile.baseCode f₀ f₁ 185364 z →
        ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z →
        Nonempty (Score6400RootedCramerObstructionData f₀ f₁ z Δ) := by
  classical
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  obtain ⟨r, rows, cols, hrows, hcols, hrank, hcomplement, hminor,
      hpolynomialKer, hdegree, hspan⟩ :=
    exists_score6400_spanning_bounded_locatorCramerFamily
      f₀ f₁ L hkernelRank
  have hcardN : Fintype.card Score6400LocatorMinorIndex = 76781 := by
    norm_num [Score6400LocatorMinorIndex, locatorOrdinaryRows6400,
      locatorFrobeniusRows6400]
  have hrle : r ≤ 76781 := by
    rw [← hcardN]
    omega
  let coordinateFamily : SelectedColumnComplement cols →
      Score6400LocatorMinorIndex → K :=
    mappedSelectedPolynomialCramerKernelVector ι M rows cols hcols
  let A := score6400SelectedLocatorCramerOrdinary
    f₀ f₁ rows cols hcols
  let B := score6400SelectedLocatorCramerFrobenius
    f₀ f₁ rows cols hcols
  have hA : ∀ j, A j ∈ Polynomial.degreeLT IRSProfile.Field[X]
      locatorOrdinaryRows6400 :=
    score6400SelectedLocatorCramerOrdinary_mem_degreeLT
      f₀ f₁ rows cols hcols
  have hB : ∀ j, B j ∈ Polynomial.degreeLT IRSProfile.Field[X]
      locatorFrobeniusRows6400 :=
    score6400SelectedLocatorCramerFrobenius_mem_degreeLT
      f₀ f₁ rows cols hcols
  let pairFamily : SelectedColumnComplement cols →
      PolynomialPairSpace K locatorOrdinaryRows6400
        locatorFrobeniusRows6400 :=
    locatorPairFamilyFraction
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 A B hA hB
  have hfamily : ∀ j, pairFamily j = e.symm (coordinateFamily j) := by
    intro j
    simpa only [pairFamily, A, B, coordinateFamily, K, ι, M,
      locatorPairFamilyFraction,
      score6400SelectedLocatorCramerOrdinary,
      score6400SelectedLocatorCramerFrobenius,
      score6400SelectedLocatorCramerVector,
      mappedSelectedPolynomialCramerKernelVector, e] using
        score6400_locatorFractionRelationPair_eq_coordinatePair
          (score6400SelectedLocatorCramerVector
            f₀ f₁ rows cols hcols j)
  have hpairLI : LinearIndependent K pairFamily := by
    simpa only [K, pairFamily, A, B] using
      linearIndependent_score6400SelectedLocatorCramerFractionPairs
        f₀ f₁ rows cols hcols hminor
  have hVrank : Module.finrank K
      (Submodule.span K (Set.range pairFamily)) = L := by
    calc
      Module.finrank K (Submodule.span K (Set.range pairFamily)) =
          Fintype.card (SelectedColumnComplement cols) :=
        finrank_span_eq_card hpairLI
      _ = Nat.card (SelectedColumnComplement cols) := by
        rw [Nat.card_eq_fintype_card]
      _ = L := hcomplement
  rcases hrankTwo with ⟨u, v, huv⟩
  have huCoordinate : e u.1 ∈
      Submodule.span K (Set.range coordinateFamily) := by
    rw [show Submodule.span K (Set.range coordinateFamily) =
        LinearMap.ker (M.map ι).mulVecLin by
      simpa only [coordinateFamily, K, ι, M] using hspan]
    have huKer := u.2
    change e u.1 ∈ LinearMap.ker (M.map ι).mulVecLin at huKer
    exact huKer
  have hvCoordinate : e v.1 ∈
      Submodule.span K (Set.range coordinateFamily) := by
    rw [show Submodule.span K (Set.range coordinateFamily) =
        LinearMap.ker (M.map ι).mulVecLin by
      simpa only [coordinateFamily, K, ι, M] using hspan]
    have hvKer := v.2
    change e v.1 ∈ LinearMap.ker (M.map ι).mulVecLin at hvKer
    exact hvKer
  have huPairRaw := symm_mem_span_range_of_mem_span_range e
    coordinateFamily (e u.1) huCoordinate
  have hvPairRaw := symm_mem_span_range_of_mem_span_range e
    coordinateFamily (e v.1) hvCoordinate
  have hfamilyEq : pairFamily =
      (fun j ↦ e.symm (coordinateFamily j)) := funext hfamily
  have huPair : u.1 ∈ Submodule.span K (Set.range pairFamily) := by
    rw [hfamilyEq]
    simpa using huPairRaw
  have hvPair : v.1 ∈ Submodule.span K (Set.range pairFamily) := by
    rw [hfamilyEq]
    simpa using hvPairRaw
  let V := Submodule.span K (Set.range pairFamily)
  have hrankTwoSpan : ∃ u v : V, polynomialPairDet u.1 v.1 ≠ 0 :=
    ⟨⟨u.1, huPair⟩, ⟨v.1, hvPair⟩, huv⟩
  have hbounded : ∀ ij, locatorPairDetCandidate A B ij ∈
      Polynomial.degreeLT IRSProfile.Field[X] 76780 := by
    intro ij
    exact score6400SelectedLocatorPairDet_mem_degreeLT_76780
      f₀ f₁ rows cols hcols ij
  have hcoeff : ∀ ij n,
      ((locatorPairDetCandidate A B ij).coeff n).natDegree ≤
        2 * (r * 2130706433) := by
    intro ij n
    exact score6400SelectedLocatorPairDet_coeff_natDegree_le
      f₀ f₁ rows cols hcols
      (by simpa only [score6400SelectedLocatorCramerVector] using hdegree)
      ij n
  have hLd : L ≤ locatorOrdinaryRows6400 + locatorFrobeniusRows6400 := by
    simpa only [locatorOrdinaryRows6400, locatorFrobeniusRows6400] using hL
  have hcut' : locatorOrdinaryRows6400 + locatorFrobeniusRows6400 - L < l := by
    simpa only [locatorOrdinaryRows6400, locatorFrobeniusRows6400] using hcut
  obtain ⟨q, hq, Δ, hΔne, hΔdegree, hΔcoeff, hΔspan⟩ :=
    exists_bounded_locatorCramerObstruction_of_pair_span_rank_two_with_span
      (c := locatorOrdinaryRows6400)
      (h := locatorFrobeniusRows6400) (D := 76780) (l := l)
      (S := 2 * (r * 2130706433)) (L := L)
      A B (by norm_num) (by norm_num) hLd hcut' hA hB
      hbounded hcoeff hl
      (by simpa only [pairFamily, V, K] using hVrank)
      (by simpa only [pairFamily, V, K] using hrankTwoSpan)
  refine ⟨r, hrle, q, hq, Δ, hΔne, hΔdegree, hΔcoeff, ?_⟩
  intro z hbad hnotOld
  let qSpecial : SelectedColumnComplement cols →
      Score6400LocatorMinorIndex → IRSProfile.Field :=
    fun j n ↦ (score6400SelectedLocatorCramerVector
      f₀ f₁ rows cols hcols j n).eval z
  have hqSpecial : ∀ j, qSpecial j ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin := by
    intro j
    apply score6400_eval_mem_locatorKernel_of_polynomial_mem_ker
      f₀ f₁ (score6400SelectedLocatorCramerVector
        f₀ f₁ rows cols hcols j)
    simpa only [score6400SelectedLocatorCramerVector] using
      hpolynomialKer j
  obtain ⟨agreementSet, P, E, hAgreementSet, hPdegree, hagreement,
      hunexplained, hE, hEcard, hEupper, hpairRoots⟩ :=
    exists_score6400_large_error_support_pairDet_roots_family
      f₀ f₁ z hbad hnotOld qSpecial hqSpecial
  refine ⟨⟨agreementSet, P, E, hAgreementSet, hPdegree, hagreement,
    hunexplained, hE, hEcard, hEupper, ?_⟩⟩
  intro i hi
  apply polynomial_map_eval_eq_zero_of_mem_span
    (Polynomial.evalRingHom z) (IRSProfile.domain i)
      (locatorPairDetCandidate A B) Δ hΔspan
  intro ij
  have hmap := score6400SelectedLocatorPairDet_map_eval
    f₀ f₁ rows cols hcols ij z
  rw [show (locatorPairDetCandidate A B ij).map
      (Polynomial.evalRingHom z) =
        polynomialPairDet
          (score6400LocatorRelationPair (qSpecial ij.1))
          (score6400LocatorRelationPair (qSpecial ij.2)) by
    simpa only [A, B, qSpecial] using hmap]
  exact hpairRoots ij.1 ij.2 i hi

/-- In the `L ≥ 11` rank-two branch the explicit Cramer construction gives
a nonzero obstruction of outer degree below every retained error support,
with the uniform coarse `20S` challenge cap. -/
theorem exists_score6400_largeNullity_rankTwo_obstruction
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlower : 11 ≤ L) (hLupper : L ≤ 76781)
    (hrankTwo : ∃ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ Δ : IRSProfile.Field[X][X], Δ ≠ 0 ∧
      Δ.natDegree < 76771 ∧
      (∀ n, (Δ.coeff n).natDegree ≤
        20 * score6400KernelBasisTotalDegree) ∧
      ∀ z : IRSProfile.Field,
        MCABad IRSProfile.baseCode f₀ f₁ 185364 z →
        ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z →
        Nonempty (Score6400RootedCramerObstructionData f₀ f₁ z Δ) := by
  obtain ⟨r, hr, q, hq, Δ, hΔne, hΔdegree, hΔcoeff, hΔroots⟩ :=
    exists_score6400_bounded_obstruction_of_locatorPairKernel_rankTwo
      f₀ f₁ L 76771 hkernelRank hLupper (by omega) (by norm_num)
        hrankTwo
  refine ⟨Δ, hΔne, hΔdegree, ?_, hΔroots⟩
  intro n
  calc
    (Δ.coeff n).natDegree ≤
        (q + 1) * (2 * (r * 2130706433)) := hΔcoeff n
    _ ≤ 20 * score6400KernelBasisTotalDegree := by
      norm_num [score6400KernelBasisTotalDegree] at hq hr ⊢
      nlinarith

/-- Every rank-two nullity `2 ≤ L ≤ 10` receives the uniform `20S` cap,
while its obstruction has outer degree at most `76780`.  The widened
exact-incidence endpoint consumes this full range. -/
theorem exists_score6400_midNullity_rankTwo_obstruction
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlower : 2 ≤ L) (hLupper : L ≤ 10)
    (hrankTwo : ∃ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ Δ : IRSProfile.Field[X][X], Δ ≠ 0 ∧
      Δ.natDegree < 76781 ∧
      (∀ n, (Δ.coeff n).natDegree ≤
        20 * score6400KernelBasisTotalDegree) ∧
      ∀ z : IRSProfile.Field,
        MCABad IRSProfile.baseCode f₀ f₁ 185364 z →
        ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z →
        Nonempty (Score6400RootedCramerObstructionData f₀ f₁ z Δ) := by
  have hLambient : L ≤ 76781 := hLupper.trans (by norm_num)
  obtain ⟨r, hr, q, hq, Δ, hΔne, hΔdegree, hΔcoeff, hΔroots⟩ :=
    exists_score6400_bounded_obstruction_of_locatorPairKernel_rankTwo
      f₀ f₁ L (76782 - L) hkernelRank hLambient
        (by omega) (by omega) hrankTwo
  have hqEight : q ≤ 8 := by omega
  refine ⟨Δ, hΔne, hΔdegree.trans_le (by omega), ?_, hΔroots⟩
  intro n
  calc
    (Δ.coeff n).natDegree ≤
        (q + 1) * (2 * (r * 2130706433)) := hΔcoeff n
    _ ≤ 20 * score6400KernelBasisTotalDegree := by
      norm_num [score6400KernelBasisTotalDegree] at hqEight hr ⊢
      nlinarith

/-- The large-nullity rational-rank-two branch is now closed quantitatively:
outside the already accepted score-63.99 bad slopes, it contains at most the
challenge degree of the rooted Cramer obstruction. -/
theorem score6400_largeNullity_rankTwo_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlower : 11 ≤ L) (hLupper : L ≤ 76781)
    (hrankTwo : ∃ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 ≠ 0)
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ 20 * score6400KernelBasisTotalDegree := by
  classical
  by_contra hTsmall
  have hTlarge : 20 * score6400KernelBasisTotalDegree < T.card := by
    omega
  obtain ⟨Δ, hΔne, hΔdegree, hΔcoeff, hΔroots⟩ :=
    exists_score6400_largeNullity_rankTwo_obstruction
      f₀ f₁ L hkernelRank hLlower hLupper hrankTwo
  have hspecial : ∀ z ∈ T,
      Δ.map (Polynomial.evalRingHom z) = 0 := by
    intro z hz
    let data := Classical.choice
      (hΔroots z (hbad z hz) (hnotOld z hz))
    let E := data.errorSet
    let Roots : Finset IRSProfile.Field := E.map IRSProfile.domain
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (Δ.map (Polynomial.evalRingHom z)) Roots
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact data.obstruction_roots i hi
    · have hdegree :
          (Δ.map (Polynomial.evalRingHom z)).natDegree < E.card :=
        Polynomial.natDegree_map_le.trans_lt
          (hΔdegree.trans_le data.errorSet_large)
      simpa only [Roots, Finset.card_map] using hdegree
  have hcoeffZero : ∀ n, Δ.coeff n = 0 := by
    intro n
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (Δ.coeff n) T
    · intro z hz
      have hzero := congrArg
        (fun P : IRSProfile.Field[X] ↦ P.coeff n) (hspecial z hz)
      simpa [Polynomial.coeff_map] using hzero
    · exact (hΔcoeff n).trans_lt hTlarge
  apply hΔne
  apply Polynomial.ext
  intro n
  simpa only [Polynomial.coeff_zero] using hcoeffZero n

end ProximityPrize.SubmissionLower

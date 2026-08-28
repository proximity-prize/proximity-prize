import ProximityPrize.SubmissionLower.BCHKSLocatorCramerRankTwoMidFinish6400
import ProximityPrize.SubmissionLower.BCHKSLocatorRootPins6400

/-!
# Nullity-one left-Cramer locator obstruction

At generic locator nullity one, the transpose kernel is also one-dimensional.
A maximal minor of the transposed polynomial locator matrix therefore produces
one bounded polynomial left-kernel vector.  Away from the pivot determinant,
every split locator supplied by an MCA-bad slope is proportional to this
single vector.  Repackaging its coordinates as a bivariate locator transfers
all genuine error roots to one fixed polynomial obstruction.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped Matrix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- The exact challenge-degree cap for a nullity-one maximal-minor vector. -/
def score6400NullityOneCramerDegree : ℕ := 76780 * 2130706433

theorem score6400NullityOneCramerDegree_eq :
    score6400NullityOneCramerDegree = 163595639925740 := by
  norm_num [score6400NullityOneCramerDegree]

/-- For a square matrix, right and left nullity agree. -/
theorem finrank_ker_transpose_mulVecLin_eq
    {K N : Type} [Field K] [Fintype N] [DecidableEq N]
    (M : Matrix N N K) :
    Module.finrank K (LinearMap.ker M.transpose.mulVecLin) =
      Module.finrank K (LinearMap.ker M.mulVecLin) := by
  have hM := M.mulVecLin.finrank_range_add_finrank_ker
  have hMt := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + Module.finrank K (LinearMap.ker M.mulVecLin) =
      Module.finrank K (N → K) at hM
  change M.transpose.rank +
      Module.finrank K (LinearMap.ker M.transpose.mulVecLin) =
        Module.finrank K (N → K) at hMt
  rw [Matrix.rank_transpose] at hMt
  omega

/-- Repackage polynomial left-kernel coordinates as one polynomial in the
evaluation-coordinate variable, with challenge polynomials as coefficients. -/
noncomputable def score6400PolynomialLeftLocator
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) :
    IRSProfile.Field[X][X] :=
  ∑ j : Score6400LocatorMinorIndex,
    Polynomial.monomial (score6400LocatorCoefficientEquiv j).1 (q j)

@[simp]
theorem score6400PolynomialLeftLocator_coeff
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (j : Score6400LocatorMinorIndex) :
    (score6400PolynomialLeftLocator q).coeff
        (score6400LocatorCoefficientEquiv j).1 = q j := by
  classical
  rw [score6400PolynomialLeftLocator, Polynomial.finsetSum_coeff]
  calc
    (∑ b, (Polynomial.monomial
        (score6400LocatorCoefficientEquiv b).1 (q b)).coeff
          (score6400LocatorCoefficientEquiv j).1) =
        (Polynomial.monomial
          (score6400LocatorCoefficientEquiv j).1 (q j)).coeff
            (score6400LocatorCoefficientEquiv j).1 := by
      apply Fintype.sum_eq_single j
      intro k hkj
      have hindex : (score6400LocatorCoefficientEquiv k).1 ≠
          (score6400LocatorCoefficientEquiv j).1 := by
        intro h
        apply hkj
        apply score6400LocatorCoefficientEquiv.injective
        exact Fin.ext h
      exact Polynomial.coeff_monomial_of_ne (q k) (Ne.symm hindex)
    _ = q j := by simp

/-- A nonzero coordinate family gives a nonzero bivariate locator. -/
theorem score6400PolynomialLeftLocator_ne_zero
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ≠ 0) : score6400PolynomialLeftLocator q ≠ 0 := by
  intro hzero
  apply hq
  funext j
  have hcoeff := congrArg
    (fun P : IRSProfile.Field[X][X] ↦
      P.coeff (score6400LocatorCoefficientEquiv j).1) hzero
  simpa using hcoeff

/-- The outer locator degree is at most the largest locator coefficient
index. -/
theorem score6400PolynomialLeftLocator_natDegree_le
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) :
    (score6400PolynomialLeftLocator q).natDegree ≤ 76780 := by
  classical
  unfold score6400PolynomialLeftLocator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le (q j)).trans (by
    have hj := (score6400LocatorCoefficientEquiv j).2
    omega)

/-- Coordinatewise challenge-degree bounds transfer to all coefficients of
the bivariate left locator. -/
theorem score6400PolynomialLeftLocator_coeff_natDegree_le
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) (S n : ℕ)
    (hq : ∀ j, (q j).natDegree ≤ S) :
    ((score6400PolynomialLeftLocator q).coeff n).natDegree ≤ S := by
  classical
  rw [score6400PolynomialLeftLocator, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  by_cases hj : (score6400LocatorCoefficientEquiv j).1 = n
  · simp [hj, hq j]
  · simp [Polynomial.coeff_monomial, hj]

/-- Evaluate both variables of the polynomial left locator. -/
theorem score6400PolynomialLeftLocator_map_eval_eval
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (z x : IRSProfile.Field) :
    ((score6400PolynomialLeftLocator q).map
        (Polynomial.evalRingHom z)).eval x =
      ∑ j : Score6400LocatorMinorIndex,
        (q j).eval z * x ^ (score6400LocatorCoefficientEquiv j).1 := by
  classical
  rw [score6400PolynomialLeftLocator, Polynomial.map_sum,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- Reindex the direct locator coefficients by the production square-matrix
coordinates. -/
noncomputable def score6400ReindexedLocator
    (locator : Fin (76780 + 1) → IRSProfile.Field) :
    Score6400LocatorMinorIndex → IRSProfile.Field :=
  fun j ↦ locator (score6400LocatorCoefficientEquiv j)

theorem score6400ReindexedLocator_ne_zero
    (locator : Fin (76780 + 1) → IRSProfile.Field)
    (hlocator : locator ≠ 0) : score6400ReindexedLocator locator ≠ 0 := by
  intro hzero
  apply hlocator
  funext j
  obtain ⟨i, rfl⟩ := score6400LocatorCoefficientEquiv.surjective j
  exact congrFun hzero i

/-- The direct Hankel locator is an explicit vector in the transpose kernel
of the selected production stack. -/
theorem score6400ReindexedLocator_mem_transpose_ker
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (locator : Fin (76780 + 1) → IRSProfile.Field)
    (hlocatorFixed : ∀ j,
      koalaSexticFrobenius (locator j) = locator j)
    (hlocatorMem : locator ∈ LinearMap.ker
      (rsSyndromeHankel IRSProfile.domain
        (fun i ↦ f₀ i + z * f₁ i)
        locatorOrdinaryRows6400 76780).mulVecLin) :
    score6400ReindexedLocator locator ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).transpose.mulVecLin := by
  classical
  have hordinary := hlocatorMem
  rw [LinearMap.mem_ker] at hordinary ⊢
  funext equation
  rcases equation with row | row
  · simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Pi.zero_apply]
    calc
      (∑ coefficient : Score6400LocatorMinorIndex,
          twoBlockSpecialization
              (score6400LocatorStackPart f₀)
              (score6400LocatorStackPart f₁)
              z (z ^ 2130706433) coefficient (Sum.inl row) *
            score6400ReindexedLocator locator coefficient) =
          ∑ j : Fin (76780 + 1),
            rsSyndromeMoment IRSProfile.domain
                (fun i ↦ f₀ i + z * f₁ i) (row.1 + j.1) * locator j := by
        apply Fintype.sum_equiv score6400LocatorCoefficientEquiv
        intro coefficient
        rw [score6400LocatorStack_specialize_ordinary]
        rfl
      _ = 0 := by
        have hrow := congrFun hordinary row
        simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
          rsSyndromeHankel, Pi.zero_apply] using hrow
  · simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Pi.zero_apply]
    let ordinaryRow : Fin locatorOrdinaryRows6400 :=
      ⟨row.1, by
        exact Nat.lt_trans row.2 (by
          norm_num [locatorOrdinaryRows6400,
            locatorFrobeniusRows6400])⟩
    have hrow := congrFun hordinary ordinaryRow
    have hrow' : ∑ j : Fin (76780 + 1),
        rsSyndromeMoment IRSProfile.domain
            (fun i ↦ f₀ i + z * f₁ i) (row.1 + j.1) * locator j = 0 := by
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        rsSyndromeHankel, Pi.zero_apply, ordinaryRow] using hrow
    calc
      (∑ coefficient : Score6400LocatorMinorIndex,
          twoBlockSpecialization
              (score6400LocatorStackPart f₀)
              (score6400LocatorStackPart f₁)
              z (z ^ 2130706433) coefficient (Sum.inr row) *
            score6400ReindexedLocator locator coefficient) =
          ∑ j : Fin (76780 + 1),
            koalaSexticFrobenius
              (rsSyndromeMoment IRSProfile.domain
                  (fun i ↦ f₀ i + z * f₁ i) (row.1 + j.1) * locator j) := by
        apply Fintype.sum_equiv score6400LocatorCoefficientEquiv
        intro coefficient
        rw [score6400LocatorStack_specialize_frobenius, map_mul,
          hlocatorFixed]
        rfl
      _ = koalaSexticFrobenius
          (∑ j : Fin (76780 + 1),
            rsSyndromeMoment IRSProfile.domain
                (fun i ↦ f₀ i + z * f₁ i) (row.1 + j.1) * locator j) := by
        rw [map_sum]
      _ = 0 := by rw [hrow', map_zero]

/-- Reindexing preserves the coordinate-evaluation sum. -/
theorem score6400ReindexedLocator_sum
    (locator : Fin (76780 + 1) → IRSProfile.Field)
    (x : IRSProfile.Field) :
    (∑ j : Score6400LocatorMinorIndex,
        score6400ReindexedLocator locator j *
          x ^ (score6400LocatorCoefficientEquiv j).1) =
      ∑ k : Fin (76780 + 1), locator k * x ^ k.1 := by
  classical
  apply Fintype.sum_equiv score6400LocatorCoefficientEquiv
  intro j
  rfl

/-- If a split locator is a nonzero scalar multiple of a specialized
left-Cramer vector, every split-locator root is a root of the bivariate
Cramer locator specialization. -/
theorem score6400PolynomialLeftLocator_root_of_reindexed_eq_smul
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (z x a : IRSProfile.Field)
    (locator : Fin (76780 + 1) → IRSProfile.Field)
    (ha : a ≠ 0)
    (hproportional : score6400ReindexedLocator locator =
      a • (fun j ↦ (q j).eval z))
    (hroot : ∑ k : Fin (76780 + 1), locator k * x ^ k.1 = 0) :
    ((score6400PolynomialLeftLocator q).map
        (Polynomial.evalRingHom z)).eval x = 0 := by
  classical
  rw [score6400PolynomialLeftLocator_map_eval_eval]
  apply (mul_eq_zero.mp (show a *
      (∑ j : Score6400LocatorMinorIndex,
        (q j).eval z * x ^ (score6400LocatorCoefficientEquiv j).1) = 0 by
    calc
      a * (∑ j : Score6400LocatorMinorIndex,
          (q j).eval z * x ^ (score6400LocatorCoefficientEquiv j).1) =
          ∑ j : Score6400LocatorMinorIndex,
            score6400ReindexedLocator locator j *
              x ^ (score6400LocatorCoefficientEquiv j).1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hj := congrFun hproportional j
        simp only [Pi.smul_apply, smul_eq_mul] at hj
        rw [hj]
        ring
      _ = ∑ k : Fin (76780 + 1), locator k * x ^ k.1 :=
        score6400ReindexedLocator_sum locator x
      _ = 0 := hroot)).resolve_left ha

/-- A decoding witness together with a split locator built from a fixed-size
subset of its original agreement set.  The genuine error set is retained so
the resulting roots can feed the existing affine-alignment endpoint. -/
structure Score6400SplitLocatorData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) where
  agreementSet : Finset IRSProfile.Index
  polynomial : IRSProfile.Field[X]
  errorSet : Finset IRSProfile.Index
  locator : Fin (76780 + 1) → IRSProfile.Field
  agreementSet_large : 185364 ≤ agreementSet.card
  polynomial_degree : polynomial.natDegree ≤ 131071
  agreement : ∀ i ∈ agreementSet,
    polynomial.eval (IRSProfile.domain i) = f₀ i + z * f₁ i
  unexplainedPair : ¬ExplainedPair
    IRSProfile.baseCode f₀ f₁ agreementSet
  errorSet_eq : errorSet = Finset.univ.filter (fun i ↦
    (f₀ i + z * f₁ i) -
      polynomial.eval (IRSProfile.domain i) ≠ 0)
  errorSet_large : 76771 ≤ errorSet.card
  errorSet_small : errorSet.card ≤ 76780
  locator_ne : locator ≠ 0
  locator_fixed : ∀ j,
    koalaSexticFrobenius (locator j) = locator j
  locator_mem : locator ∈ LinearMap.ker
    (rsSyndromeHankel IRSProfile.domain
      (fun i ↦ f₀ i + z * f₁ i)
      locatorOrdinaryRows6400 76780).mulVecLin
  error_locator_roots : ∀ i ∈ errorSet,
    ∑ j : Fin (76780 + 1),
      locator j * IRSProfile.domain i ^ j.1 = 0

/-- Every retained bad slope has a large genuine-error set and a compatible
split locator coming from the same decoding witness. -/
theorem exists_score6400_split_locator_data
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    Nonempty (Score6400SplitLocatorData f₀ f₁ z) := by
  classical
  rcases hbad with ⟨A, hA, ⟨c, hc, hcAgree⟩, hpair⟩
  have hcRS : c ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension := by
    simpa only [IRSProfile.baseCode] using hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcRS
  obtain ⟨P, hPdegree, hPc⟩ := hcRS
  subst c
  have hPagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    exact hcAgree i hi
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · subst P
      norm_num
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  let E : Finset IRSProfile.Index := Finset.univ.filter fun i ↦
    (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i ↦
    P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i
  have hAG : A ⊆ G := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPagree i hi⟩
  have hpartition : E.card + G.card = 262144 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun i : IRSProfile.Index ↦
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0)
      (s := Finset.univ)
    have hsecond : (Finset.univ.filter fun i : IRSProfile.Index ↦
        ¬((f₀ i + z * f₁ i) -
          P.eval (IRSProfile.domain i) ≠ 0)) = G := by
      ext i
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and,
        not_ne_iff, sub_eq_zero]
      exact eq_comm
    rw [show (Finset.univ.filter fun i : IRSProfile.Index ↦
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0) = E
          by rfl, hsecond] at hsplit
    calc
      E.card + G.card = Finset.univ.card := hsplit
      _ = 262144 := by norm_num [IRSProfile.Index]
  have hElarge : 76771 ≤ E.card := by
    by_contra hsmall
    have hGlarge : 185374 ≤ G.card := by omega
    apply hnotOld
    refine ⟨G, hGlarge, ?_, ?_⟩
    · refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain P, ?_, ?_⟩
      · simpa only [IRSProfile.baseCode] using
          (show ReedSolomon.evalOnPoints IRSProfile.domain P ∈
            ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension by
              rw [ReedSolomon.mem_code_iff_exists_polynomial]
              exact ⟨P, hPdegree, rfl⟩)
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
    · intro hpairG
      apply hpair
      rcases hpairG with ⟨c₀, hc₀, c₁, hc₁, h₀, h₁⟩
      exact ⟨c₀, hc₀, c₁, hc₁,
        (fun i hi ↦ h₀ i (hAG hi)),
        (fun i hi ↦ h₁ i (hAG hi))⟩
  have hEsmall : E.card ≤ 76780 := by
    have hAleG : A.card ≤ G.card := Finset.card_le_card hAG
    omega
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hA
  let SplitE : Finset IRSProfile.Index := Finset.univ \ A'
  have hSplitEcard : SplitE.card = 76780 := by
    dsimp only [SplitE]
    rw [Finset.card_sdiff]
    norm_num [hA'card, IRSProfile.Index]
  have hPagree' : ∀ i ∈ A',
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    exact hPagree i (hA'sub hi)
  have hlocatorDegree :
      (rsAgreementLocator IRSProfile.domain A').natDegree = 76780 := by
    rw [rsAgreementLocator_natDegree]
    exact hSplitEcard
  let locator := rsLocatorCoefficients IRSProfile.domain A' 76780
  have hlocatorNe : locator ≠ 0 :=
    rsLocatorCoefficients_ne_zero IRSProfile.domain A' 76780
      hlocatorDegree.le
  have hlocatorFixed : ∀ j,
      koalaSexticFrobenius (locator j) = locator j := by
    intro j
    simpa only [locator, rsLocatorCoefficients] using
      map_rsAgreementLocator_coeff IRSProfile.domain
        koalaSexticFrobenius koalaSexticFrobenius_fixed_domain A' j.1
  have hdegreeRoom :
      (Finset.univ \ A').card + P.natDegree + locatorOrdinaryRows6400 ≤
        Fintype.card IRSProfile.Index - 1 := by
    rw [show (Finset.univ \ A').card = 76780 by
      simpa only [SplitE] using hSplitEcard]
    norm_num [locatorOrdinaryRows6400, IRSProfile.Index]
    omega
  have hlocatorMem : locator ∈ LinearMap.ker
      (rsSyndromeHankel IRSProfile.domain
        (fun i ↦ f₀ i + z * f₁ i)
        locatorOrdinaryRows6400 76780).mulVecLin :=
    rsLocatorCoefficients_mem_hankel_ker
      IRSProfile.domain A' (fun i ↦ f₀ i + z * f₁ i) P hPagree'
      locatorOrdinaryRows6400 76780 hlocatorDegree.le hdegreeRoom
  have herrorRoots : ∀ i ∈ E,
      ∑ j : Fin (76780 + 1),
        locator j * IRSProfile.domain i ^ j.1 = 0 := by
    intro i hiE
    have hiError : (f₀ i + z * f₁ i) -
        P.eval (IRSProfile.domain i) ≠ 0 := by
      change i ∈ Finset.univ.filter (fun k : IRSProfile.Index ↦
        (f₀ k + z * f₁ k) - P.eval (IRSProfile.domain k) ≠ 0) at hiE
      exact (Finset.mem_filter.mp hiE).2
    have hiA' : i ∉ A' := by
      intro hi
      exact hiError (by rw [hPagree' i hi, sub_self])
    have hroot := rsAgreementLocator_eval_eq_zero_of_not_mem
      IRSProfile.domain A' hiA'
    calc
      (∑ j : Fin (76780 + 1),
          locator j * IRSProfile.domain i ^ j.1) =
          (rsAgreementLocator IRSProfile.domain A').eval
            (IRSProfile.domain i) := by
        rw [Polynomial.eval_eq_sum_range'
          (Nat.lt_succ_of_le hlocatorDegree.le)]
        rw [← Fin.sum_univ_eq_sum_range]
        rfl
      _ = 0 := hroot
  exact ⟨⟨A, P, E, locator, hA, hPnat, hPagree, hpair, rfl,
    hElarge, hEsmall, hlocatorNe, hlocatorFixed, hlocatorMem,
    herrorRoots⟩⟩

/-- Global nullity-one Cramer data.  The pivot polynomial owns the exceptional
slopes; at every other retained bad slope, the bivariate locator has the
full genuine-error root set required by the alignment finish. -/
structure Score6400NullityOneCramerData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) where
  pivot : IRSProfile.Field[X]
  obstruction : IRSProfile.Field[X][X]
  pivot_ne : pivot ≠ 0
  pivot_degree : pivot.natDegree ≤ score6400NullityOneCramerDegree
  obstruction_ne : obstruction ≠ 0
  obstruction_degree : obstruction.natDegree ≤ 76780
  obstruction_coeff_degree : ∀ n,
    (obstruction.coeff n).natDegree ≤ score6400NullityOneCramerDegree
  specialization_ne : ∀ z : IRSProfile.Field, pivot.eval z ≠ 0 →
    obstruction.map (Polynomial.evalRingHom z) ≠ 0
  rooted : ∀ z : IRSProfile.Field, pivot.eval z ≠ 0 →
    MCABad IRSProfile.baseCode f₀ f₁ 185364 z →
    ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z →
    Nonempty (Score6400RootedCramerObstructionData
      f₀ f₁ z obstruction)

/-- Generic nullity one produces one bounded global left-Cramer locator. -/
theorem exists_score6400_nullityOneCramerData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = 1) :
    Nonempty (Score6400NullityOneCramerData f₀ f₁) := by
  classical
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  have hleftKernelRank : Module.finrank K
      (LinearMap.ker ((M.transpose).map ι).mulVecLin) = 1 := by
    have htranspose := finrank_ker_transpose_mulVecLin_eq (M.map ι)
    rw [← Matrix.transpose_map] at htranspose
    exact htranspose.trans (by simpa only [K, ι, M] using hkernelRank)
  obtain ⟨r, rows, cols, hrows, hcols, hrank, hcomplement,
      hminor, hspanGeneric, hdegree⟩ :=
    exists_spanning_bounded_polynomialCramerKernelFamily
      ι M.transpose 1 2130706433 hleftKernelRank (by
        intro i j
        simpa only [Matrix.transpose_apply] using
          score6400LocatorPolynomialMatrix_entry_natDegree_le f₀ f₁ j i)
  have hr : r = 76780 := by
    norm_num [Score6400LocatorMinorIndex, locatorOrdinaryRows6400,
      locatorFrobeniusRows6400] at hrank
    omega
  obtain ⟨j₀, hj₀⟩ := Nat.card_eq_one_iff_exists.mp hcomplement
  let q : Score6400LocatorMinorIndex → IRSProfile.Field[X] :=
    selectedPolynomialCramerKernelVector M.transpose rows cols hcols j₀
  let D : IRSProfile.Field[X] :=
    (selectedPolynomialPivotBlock M.transpose rows cols).det
  let Δ : IRSProfile.Field[X][X] := score6400PolynomialLeftLocator q
  have hDne : D ≠ 0 := by
    intro hzero
    apply hminor
    simp only [D, hzero, map_zero]
  have hDdegree : D.natDegree ≤ score6400NullityOneCramerDegree := by
    have hfree := hdegree j₀ j₀.1
    rw [selectedPolynomialCramerKernelVector_apply_free, if_pos rfl] at hfree
    simpa only [D, score6400NullityOneCramerDegree, hr] using hfree
  have hqdegree : ∀ n, (q n).natDegree ≤
      score6400NullityOneCramerDegree := by
    intro n
    simpa only [q, score6400NullityOneCramerDegree, hr] using hdegree j₀ n
  have hqne : q ≠ 0 := by
    intro hzero
    apply hDne
    have hfree := congrFun hzero j₀.1
    rw [show q j₀.1 = D by
      simp only [q, D, selectedPolynomialCramerKernelVector_apply_free,
        if_pos]] at hfree
    exact hfree
  have hΔne : Δ ≠ 0 := score6400PolynomialLeftLocator_ne_zero q hqne
  have hΔdegree : Δ.natDegree ≤ 76780 :=
    score6400PolynomialLeftLocator_natDegree_le q
  have hΔcoeff : ∀ n, (Δ.coeff n).natDegree ≤
      score6400NullityOneCramerDegree := by
    intro n
    exact score6400PolynomialLeftLocator_coeff_natDegree_le
      q score6400NullityOneCramerDegree n hqdegree
  refine ⟨⟨D, Δ, hDne, hDdegree, hΔne, hΔdegree, hΔcoeff, ?_, ?_⟩⟩
  · intro z hDz
    apply polynomial_map_ne_zero_of_coeff_eval_ne_zero
      Δ (score6400LocatorCoefficientEquiv j₀).1 z
    rw [show Δ.coeff (score6400LocatorCoefficientEquiv j₀).1 = D by
      simp only [Δ, score6400PolynomialLeftLocator_coeff, q, D,
        selectedPolynomialCramerKernelVector_apply_free, if_pos]]
    exact hDz
  intro z hDz hbad hnotOld
  let d : Score6400SplitLocatorData f₀ f₁ z :=
    Classical.choice (exists_score6400_split_locator_data
      f₀ f₁ z hbad hnotOld)
  let evalz : IRSProfile.Field[X] →+* IRSProfile.Field :=
    Polynomial.evalRingHom z
  let FullKer : Submodule IRSProfile.Field
      (Score6400LocatorMinorIndex → IRSProfile.Field) :=
    LinearMap.ker (((M.transpose).map evalz).mulVecLin)
  let TopKer : Submodule IRSProfile.Field
      (Score6400LocatorMinorIndex → IRSProfile.Field) :=
    LinearMap.ker
      ((((M.transpose).submatrix rows (Equiv.refl _)).map evalz).mulVecLin)
  have hdetz : evalz
      (selectedPolynomialPivotBlock M.transpose rows cols).det ≠ 0 := by
    simpa [evalz, D] using hDz
  have hlocatorMemConcrete :=
    score6400ReindexedLocator_mem_transpose_ker
      f₀ f₁ z d.locator d.locator_fixed d.locator_mem
  have hspecialization : (M.transpose).map evalz =
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).transpose := by
    rw [Matrix.transpose_map]
    simpa only [M, evalz] using congrArg Matrix.transpose
      (score6400LocatorPolynomialMatrix_map_eval f₀ f₁ z)
  have hlocatorMem : score6400ReindexedLocator d.locator ∈ FullKer := by
    simpa only [FullKer, hspecialization] using hlocatorMemConcrete
  have hlocatorNe : score6400ReindexedLocator d.locator ≠ 0 :=
    score6400ReindexedLocator_ne_zero d.locator d.locator_ne
  have hfullLeTop : FullKer ≤ TopKer := by
    exact fullMatrix_ker_le_selectedRows_ker evalz M.transpose rows
  have htopRank : Module.finrank IRSProfile.Field TopKer = 1 := by
    have htop := finrank_selectedRows_ker_eq_card_complement
      evalz M.transpose rows cols hcols hdetz
    simpa only [TopKer, hcomplement] using htop
  have hfullNonbot : FullKer ≠ ⊥ := by
    intro hbot
    apply hlocatorNe
    have : score6400ReindexedLocator d.locator ∈
        (⊥ : Submodule IRSProfile.Field
          (Score6400LocatorMinorIndex → IRSProfile.Field)) := by
      rw [← hbot]
      exact hlocatorMem
    simpa using this
  have hfullRank : Module.finrank IRSProfile.Field FullKer = 1 := by
    have hlower : 1 ≤ Module.finrank IRSProfile.Field FullKer :=
      Submodule.one_le_finrank_iff.mpr hfullNonbot
    have hupper := Submodule.finrank_mono hfullLeTop
    rw [htopRank] at hupper
    omega
  have hspanSpecialized :=
    span_mappedSelectedPolynomialCramerKernelVector_eq_full_ker
      evalz M.transpose rows cols hcols hdetz (by
        simpa only [FullKer, hcomplement] using hfullRank)
  let family : SelectedColumnComplement cols →
      Score6400LocatorMinorIndex → IRSProfile.Field :=
    mappedSelectedPolynomialCramerKernelVector
      evalz M.transpose rows cols hcols
  have hrange : Set.range family = {family j₀} := by
    ext v
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rw [hj₀ j]
    · intro hv
      exact ⟨j₀, hv.symm⟩
  have hlocatorSpan : score6400ReindexedLocator d.locator ∈
      Submodule.span IRSProfile.Field {family j₀} := by
    rw [← hrange, hspanSpecialized]
    exact hlocatorMem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hlocatorSpan
  have hane : a ≠ 0 := by
    intro hazero
    apply hlocatorNe
    rw [← ha, hazero, zero_smul]
  have hproportional : score6400ReindexedLocator d.locator =
      a • (fun j ↦ (q j).eval z) := by
    rw [← ha]
    congr 1
  refine ⟨⟨d.agreementSet, d.polynomial, d.errorSet,
    d.agreementSet_large, d.polynomial_degree, d.agreement,
    d.unexplainedPair, d.errorSet_eq, d.errorSet_large, d.errorSet_small,
    ?_⟩⟩
  intro i hi
  exact score6400PolynomialLeftLocator_root_of_reindexed_eq_smul
    q z (IRSProfile.domain i) a d.locator hane hproportional
      (d.error_locator_roots i hi)

/-- Exact incidence margin after deleting all roots of the nullity-one pivot
polynomial. -/
theorem score6400_nullityOne_incidence_numeric
    (tcard : ℕ) (ht : 174808552391494020 < tcard) :
    262144 * score6400NullityOneCramerDegree <
      (76771 - 49633) * tcard := by
  norm_num [score6400NullityOneCramerDegree] at ht ⊢
  nlinarith

/-- The lower degree cap of the nullity-one left locator forces a slightly
larger fixed coordinate container than the rank-two obstruction needed. -/
theorem exists_score6400_nullityOne_fixed_container
    (Δ : IRSProfile.Field[X][X]) (hΔne : Δ ≠ 0)
    (hΔcoeff : ∀ n, (Δ.coeff n).natDegree ≤
      score6400NullityOneCramerDegree)
    (T : Finset IRSProfile.Field)
    (hT : 174808552391494020 < T.card)
    (E : IRSProfile.Field → Finset IRSProfile.Index)
    (hEcard : ∀ z ∈ T, 76771 ≤ (E z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ E z,
      (Δ.map (Polynomial.evalRingHom z)).eval
        (IRSProfile.domain i) = 0) :
    ∃ Container : Finset IRSProfile.Index,
      Container = Finset.univ.filter (fun i ↦
        score6400CramerCoordinateObstruction Δ i = 0) ∧
      49634 ≤ Container.card ∧ Container.card ≤ Δ.natDegree := by
  classical
  let G : IRSProfile.Index → IRSProfile.Field[X] :=
    score6400CramerCoordinateObstruction Δ
  let Container : Finset IRSProfile.Index :=
    Finset.univ.filter fun i ↦ G i = 0
  have hGdegree : ∀ i,
      (G i).natDegree ≤ score6400NullityOneCramerDegree := by
    intro i
    exact score6400CramerCoordinateObstruction_natDegree_le
      Δ score6400NullityOneCramerDegree hΔcoeff i
  have hGroot : ∀ z ∈ T, ∀ i ∈ E z, (G i).eval z = 0 := by
    intro z hz i hi
    rw [show G i = score6400CramerCoordinateObstruction Δ i by rfl,
      score6400CramerCoordinateObstruction_eval]
    exact hroot z hz i hi
  have hContainerLower : 49634 ≤ Container.card := by
    obtain ⟨z, hzT, hzlarge⟩ :=
      exists_many_zero_obstruction_agreements
        T E G 262144 76771 49633 score6400NullityOneCramerDegree
        (by norm_num [IRSProfile.Index]) hEcard
        (fun z hz i hi ↦ Or.inr (hGroot z hz i hi)) hGdegree
        (score6400_nullityOne_incidence_numeric T.card hT)
    have hsub : (E z).filter (fun i ↦ G i = 0) ⊆
        Finset.univ.filter (fun i : IRSProfile.Index ↦ G i = 0) := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
    simpa only [Container] using hzlarge.trans (Finset.card_le_card hsub)
  have hContainerUpper : Container.card ≤ Δ.natDegree := by
    by_contra hlarge
    have hdegree : Δ.natDegree < Container.card := by omega
    let domainC : IRSProfile.Index ↪ IRSProfile.Field[X] :=
      ⟨fun i ↦ Polynomial.C (IRSProfile.domain i), by
        intro i j hij
        apply IRSProfile.domain.injective
        exact Polynomial.C_injective hij⟩
    let Roots : Finset IRSProfile.Field[X] := Container.map domainC
    apply hΔne
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Δ Roots
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hiZero : G i = 0 := (Finset.mem_filter.mp hi).2
      change Δ.eval (Polynomial.C (IRSProfile.domain i)) = 0
      simpa only [G, score6400CramerCoordinateObstruction] using hiZero
    · simpa only [Roots, Finset.card_map] using hdegree
  exact ⟨Container, rfl, hContainerLower, hContainerUpper⟩

theorem score6400_nullityOne_fixed_container_room
    (c : ℕ) (hlower : 49634 ≤ c) (hupper : c ≤ 76780) :
    131072 + c + 3 * (76780 - c) ≤ 262144 := by
  omega

/-- The complete generic-nullity-one branch.  Pivot-root deletion, exact
incidence, and fixed-container affine alignment together give the target
new-slope budget. -/
theorem score6400_nullityOne_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = 1)
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ 174972148031419760 := by
  classical
  by_contra hTsmall
  have hTlarge : 174972148031419760 < T.card := by omega
  let d : Score6400NullityOneCramerData f₀ f₁ :=
    Classical.choice (exists_score6400_nullityOneCramerData
      f₀ f₁ hkernelRank)
  let Good : Finset IRSProfile.Field :=
    T.filter fun z ↦ d.pivot.eval z ≠ 0
  have hGoodT : Good ⊆ T := Finset.filter_subset _ _
  have hGoodCount :=
    card_le_filter_polynomial_eval_ne_zero_add_natDegree
      T d.pivot d.pivot_ne
  change T.card ≤ Good.card + d.pivot.natDegree at hGoodCount
  have hGoodLarge : 174808552391494020 < Good.card := by
    have hpivotDegree := d.pivot_degree
    norm_num [score6400NullityOneCramerDegree] at hpivotDegree
    omega
  let data : (z : {z // z ∈ Good}) →
      Score6400RootedCramerObstructionData
        f₀ f₁ z.1 d.obstruction :=
    fun z ↦ Classical.choice
      (d.rooted z.1 (Finset.mem_filter.mp z.2).2
        (hbad z.1 (hGoodT z.2)) (hnotOld z.1 (hGoodT z.2)))
  let E : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    if hz : z ∈ Good then (data ⟨z, hz⟩).errorSet else ∅
  have hEcard : ∀ z ∈ Good, 76771 ≤ (E z).card := by
    intro z hz
    rw [show E z = (data ⟨z, hz⟩).errorSet by simp [E, hz]]
    exact (data ⟨z, hz⟩).errorSet_large
  have hEroot : ∀ z ∈ Good, ∀ i ∈ E z,
      (d.obstruction.map (Polynomial.evalRingHom z)).eval
        (IRSProfile.domain i) = 0 := by
    intro z hz i hi
    rw [show E z = (data ⟨z, hz⟩).errorSet by simp [E, hz]] at hi
    exact (data ⟨z, hz⟩).obstruction_roots i hi
  obtain ⟨C, hCeq, hClower, hCupper⟩ :=
    exists_score6400_nullityOne_fixed_container
      d.obstruction d.obstruction_ne d.obstruction_coeff_degree
      Good hGoodLarge E hEcard hEroot
  have hCupper' : C.card ≤ 76780 := hCupper.trans d.obstruction_degree
  have hspecialNe : ∀ z ∈ Good,
      d.obstruction.map (Polynomial.evalRingHom z) ≠ 0 := by
    intro z hz
    exact d.specialization_ne z (Finset.mem_filter.mp hz).2
  let RootSet : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    Finset.univ.filter fun i ↦
      (d.obstruction.map (Polynomial.evalRingHom z)).eval
        (IRSProfile.domain i) = 0
  let R : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    RootSet z \ C
  let A : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    if hz : z ∈ Good then (data ⟨z, hz⟩).agreementSet else ∅
  let P : IRSProfile.Field → IRSProfile.Field[X] := fun z ↦
    if hz : z ∈ Good then (data ⟨z, hz⟩).polynomial else 0
  have hCroot : ∀ z, C ⊆ RootSet z := by
    intro z i hi
    rw [hCeq] at hi
    have hiCoordinate := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    rw [← score6400CramerCoordinateObstruction_eval
      d.obstruction i z, hiCoordinate, Polynomial.eval_zero]
  have hRootCard : ∀ z ∈ Good,
      (RootSet z).card ≤ d.obstruction.natDegree := by
    intro z hz
    calc
      (RootSet z).card ≤
          (d.obstruction.map
            (Polynomial.evalRingHom z)).natDegree := by
        simpa only [RootSet] using
          score6400_domain_rootSet_card_le_natDegree
            (d.obstruction.map (Polynomial.evalRingHom z))
              (hspecialNe z hz)
      _ ≤ d.obstruction.natDegree := Polynomial.natDegree_map_le
  have hRcard : ∀ z ∈ Good, (R z).card ≤ 76780 - C.card := by
    intro z hz
    have hpartition := Finset.card_sdiff_add_card_eq_card (hCroot z)
    have hcap := hRootCard z hz
    have hdegreecap := d.obstruction_degree
    change (RootSet z \ C).card ≤ 76780 - C.card
    omega
  have hAeq : ∀ z (hz : z ∈ Good),
      A z = (data ⟨z, hz⟩).agreementSet := by
    intro z hz
    simp only [A, dif_pos hz]
  have hPeq : ∀ z (hz : z ∈ Good),
      P z = (data ⟨z, hz⟩).polynomial := by
    intro z hz
    simp only [P, dif_pos hz]
  have hAcard : ∀ z ∈ Good,
      Fintype.card IRSProfile.Index - 76780 ≤ (A z).card := by
    intro z hz
    rw [hAeq z hz]
    norm_num [IRSProfile.Index]
    exact (data ⟨z, hz⟩).agreementSet_large
  have hPdegree : ∀ z ∈ Good, (P z).natDegree < 131072 := by
    intro z hz
    rw [hPeq z hz]
    exact (data ⟨z, hz⟩).polynomial_degree.trans_lt (by norm_num)
  have hPagree : ∀ z ∈ Good, ∀ i ∈ A z,
      (P z).eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro z hz i hi
    rw [hAeq z hz] at hi
    rw [hPeq z hz]
    exact (data ⟨z, hz⟩).agreement i hi
  have houtside : ∀ z ∈ Good, ∀ i, i ∉ C → i ∉ R z →
      (P z).eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro z hz i hiC hiR
    rw [hPeq z hz]
    let dz := data ⟨z, hz⟩
    have hiNotError : i ∉ dz.errorSet := by
      intro hiError
      apply hiR
      refine Finset.mem_sdiff.mpr ⟨?_, hiC⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      exact dz.obstruction_roots i hiError
    have hnot : ¬((f₀ i + z * f₁ i) -
        dz.polynomial.eval (IRSProfile.domain i) ≠ 0) := by
      rw [dz.errorSet_eq] at hiNotError
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hiNotError
    have heq : (f₀ i + z * f₁ i) -
        dz.polynomial.eval (IRSProfile.domain i) = 0 := not_ne_iff.mp hnot
    exact (sub_eq_zero.mp heq).symm
  have htwo : 1 < Good.card := by omega
  obtain ⟨z₀, hz₀, z₁, hz₁, hzne⟩ := Finset.one_lt_card.mp htwo
  have hroom : 131072 + C.card + 3 * (76780 - C.card) ≤
      Fintype.card IRSProfile.Index := by
    norm_num [IRSProfile.Index]
    exact score6400_nullityOne_fixed_container_room
      C.card hClower hCupper'
  obtain ⟨p₀, p₁, hp₀, hp₁, z, hz, hcommon⟩ :=
    exists_common_pair_agreement_of_fixed_error_container
      IRSProfile.domain Good A P f₀ f₁ C R
        131072 (76780 - C.card) 76780 z₀ z₁ hz₀ hz₁ hzne
        (by omega) hAcard hPdegree hPagree hRcard
        houtside hroom
  let dz := data ⟨z, hz⟩
  have hAz : A z = dz.agreementSet := by
    simpa only [dz] using hAeq z hz
  apply dz.unexplainedPair
  refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₀, ?_,
    ReedSolomon.evalOnPoints IRSProfile.domain p₁, ?_, ?_, ?_⟩
  · change ReedSolomon.evalOnPoints IRSProfile.domain p₀ ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    exact score6400_degree_lt_baseDimension_of_natDegree_lt hp₀
  · change ReedSolomon.evalOnPoints IRSProfile.domain p₁ ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    exact score6400_degree_lt_baseDimension_of_natDegree_lt hp₁
  · intro i hi
    change p₀.eval (IRSProfile.domain i) = f₀ i
    exact (hcommon i (hAz.symm ▸ hi)).1.symm
  · intro i hi
    change p₁.eval (IRSProfile.domain i) = f₁ i
    exact (hcommon i (hAz.symm ▸ hi)).2.symm

end ProximityPrize.SubmissionLower

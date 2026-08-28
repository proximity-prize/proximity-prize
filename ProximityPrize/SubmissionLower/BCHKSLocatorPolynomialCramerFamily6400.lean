import ProximityPrize.SubmissionLower.BCHKSPolynomialMatrixCramerKernel6400
import ProximityPrize.SubmissionLower.BCHKSLocatorRelationProduction6400

/-!
# Explicit polynomial Cramer families for the production locator pencil

This module instantiates the abstract maximal-minor Cramer construction for
the actual `76781`-square score-64 locator pencil.  Its polynomial variable is
the affine challenge.  Evaluating a polynomial kernel vector at a challenge
therefore gives a concrete locator relation at that slope.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped Matrix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark

/-- Entrywise degree bound for a diagonal two-block Frobenius pencil. -/
theorem twoBlockFrobeniusPencil_entry_natDegree_le
    {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (p : ℕ) (hp : 1 ≤ p)
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K)
    (i j : I ⊕ J) :
    (twoBlockFrobeniusPencil p base slope i j).natDegree ≤ p := by
  cases j <;>
    simp [twoBlockFrobeniusPencil] <;>
    compute_degree <;>
    omega

/-- Point evaluation of the diagonal polynomial pencil is its two-block
specialization on `(z,z^p)`. -/
theorem twoBlockFrobeniusPencil_map_eval
    {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (p : ℕ) (base slope : Matrix (I ⊕ J) (I ⊕ J) K) (z : K) :
    (twoBlockFrobeniusPencil p base slope).map
        (Polynomial.evalRingHom z) =
      twoBlockSpecialization base slope z (z ^ p) := by
  ext i j
  cases j with
  | inl j =>
      change (Polynomial.C (base i (Sum.inl j)) +
          Polynomial.X * Polynomial.C (slope i (Sum.inl j))).eval z =
        base i (Sum.inl j) + z * slope i (Sum.inl j)
      simp only [Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]
  | inr j =>
      change (Polynomial.C (base i (Sum.inr j)) +
          Polynomial.X ^ p * Polynomial.C (slope i (Sum.inr j))).eval z =
        base i (Sum.inr j) + z ^ p * slope i (Sum.inr j)
      simp only [Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- The diagonal production locator pencil, viewed as a univariate polynomial
matrix in the affine challenge. -/
noncomputable def score6400LocatorPolynomialMatrix
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    Matrix Score6400LocatorMinorIndex Score6400LocatorMinorIndex
      IRSProfile.Field[X] :=
  twoBlockFrobeniusPencil 2130706433
    (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)

/-- Every production-pencil entry has challenge degree at most `p`. -/
theorem score6400LocatorPolynomialMatrix_entry_natDegree_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i j : Score6400LocatorMinorIndex) :
    (score6400LocatorPolynomialMatrix f₀ f₁ i j).natDegree ≤
      2130706433 := by
  exact twoBlockFrobeniusPencil_entry_natDegree_le
    2130706433 (by norm_num) _ _ i j

/-- Evaluating the polynomial locator matrix is exactly concrete Frobenius
specialization. -/
theorem score6400LocatorPolynomialMatrix_map_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    (score6400LocatorPolynomialMatrix f₀ f₁).map
        (Polynomial.evalRingHom z) =
      twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433) := by
  exact twoBlockFrobeniusPencil_map_eval 2130706433 _ _ z

/-- A polynomial kernel identity specializes to a concrete locator-kernel
identity at every challenge. -/
theorem score6400_eval_mem_locatorKernel_of_polynomial_mem_ker
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (z : IRSProfile.Field) :
    (fun i ↦ (q i).eval z) ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin := by
  rw [LinearMap.mem_ker] at hq ⊢
  rw [← score6400LocatorPolynomialMatrix_map_eval]
  change
    ((score6400LocatorPolynomialMatrix f₀ f₁).map
        (Polynomial.evalRingHom z)) *ᵥ
      ((Polynomial.evalRingHom z) ∘ q) = 0
  funext i
  rw [← RingHom.map_mulVec]
  have hi := congrFun hq i
  simpa using congrArg (Polynomial.evalRingHom z) hi

/-- Coefficient coordinates for two bounded polynomial blocks over an
arbitrary commutative coefficient ring. -/
noncomputable def polynomialPairCoordinateEquiv
    (R : Type) [CommRing R] (c h : ℕ) :
    ((Polynomial.degreeLT R c) × (Polynomial.degreeLT R h)) ≃ₗ[R]
      ((Fin c ⊕ Fin h) → R) :=
  LinearEquiv.prodCongr
      (Polynomial.degreeLTEquiv R c) (Polynomial.degreeLTEquiv R h) ≪≫ₗ
    (LinearEquiv.sumArrowLequivProdArrow
      (Fin c) (Fin h) R R).symm

@[simp]
theorem degreeLTEquiv_apply_eq_coeff
    {R : Type} [Semiring R] {d : ℕ}
    (P : Polynomial.degreeLT R d) (i : Fin d) :
    Polynomial.degreeLTEquiv R d P i = P.1.coeff i := rfl

/-- Repackage polynomial-valued locator coordinates as two bivariate
multiplier polynomials.  This is the coefficient-ring analogue of
`score6400LocatorRelationPair`. -/
noncomputable def score6400PolynomialLocatorRelationPair
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) :
    (Polynomial.degreeLT IRSProfile.Field[X] locatorOrdinaryRows6400) ×
      (Polynomial.degreeLT IRSProfile.Field[X]
        locatorFrobeniusRows6400) :=
  (polynomialPairCoordinateEquiv IRSProfile.Field[X]
    locatorOrdinaryRows6400 locatorFrobeniusRows6400).symm q

@[simp]
theorem score6400PolynomialLocatorRelationPair_inl_coeff
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : Fin locatorOrdinaryRows6400) :
    (Polynomial.degreeLTEquiv IRSProfile.Field[X]
      locatorOrdinaryRows6400
      (score6400PolynomialLocatorRelationPair q).1) i = q (Sum.inl i) := by
  have h := congrFun
    ((polynomialPairCoordinateEquiv IRSProfile.Field[X]
      locatorOrdinaryRows6400 locatorFrobeniusRows6400).apply_symm_apply q)
      (Sum.inl i)
  simpa only [score6400PolynomialLocatorRelationPair,
    polynomialPairCoordinateEquiv,
    LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl] using h

@[simp]
theorem score6400PolynomialLocatorRelationPair_inr_coeff
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : Fin locatorFrobeniusRows6400) :
    (Polynomial.degreeLTEquiv IRSProfile.Field[X]
      locatorFrobeniusRows6400
      (score6400PolynomialLocatorRelationPair q).2) i = q (Sum.inr i) := by
  have h := congrFun
    ((polynomialPairCoordinateEquiv IRSProfile.Field[X]
      locatorOrdinaryRows6400 locatorFrobeniusRows6400).apply_symm_apply q)
      (Sum.inr i)
  simpa only [score6400PolynomialLocatorRelationPair,
    polynomialPairCoordinateEquiv,
    LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr] using h

/-- Challenge evaluation commutes with the ordinary multiplier assembled
from polynomial-valued coordinates. -/
theorem score6400PolynomialLocatorRelationPair_fst_map_eval
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (z : IRSProfile.Field) :
    (score6400PolynomialLocatorRelationPair q).1.1.map
        (Polynomial.evalRingHom z) =
      (score6400LocatorRelationPair (fun i ↦ (q i).eval z)).1.1 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map]
  by_cases hn : n < locatorOrdinaryRows6400
  · let i : Fin locatorOrdinaryRows6400 := ⟨n, hn⟩
    have hp := score6400PolynomialLocatorRelationPair_inl_coeff q i
    have hs := score6400LocatorRelationPair_inl_coeff
      (fun k ↦ (q k).eval z) i
    rw [degreeLTEquiv_apply_eq_coeff] at hp hs
    simp only [i] at hp hs
    rw [hp, hs]
    rfl
  · have hnle : locatorOrdinaryRows6400 ≤ n := Nat.le_of_not_gt hn
    have hpzero :
        (score6400PolynomialLocatorRelationPair q).1.1.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        ((Polynomial.mem_degreeLT.mp
          (score6400PolynomialLocatorRelationPair q).1.2).trans_le
            (WithBot.coe_le_coe.mpr hnle))
    have hszero :
        (score6400LocatorRelationPair
          (fun k ↦ (q k).eval z)).1.1.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        ((Polynomial.mem_degreeLT.mp
          (score6400LocatorRelationPair
            (fun k ↦ (q k).eval z)).1.2).trans_le
              (WithBot.coe_le_coe.mpr hnle))
    simp only [hpzero, hszero, map_zero]

/-- Challenge evaluation commutes with the Frobenius multiplier assembled
from polynomial-valued coordinates. -/
theorem score6400PolynomialLocatorRelationPair_snd_map_eval
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (z : IRSProfile.Field) :
    (score6400PolynomialLocatorRelationPair q).2.1.map
        (Polynomial.evalRingHom z) =
      (score6400LocatorRelationPair (fun i ↦ (q i).eval z)).2.1 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map]
  by_cases hn : n < locatorFrobeniusRows6400
  · let i : Fin locatorFrobeniusRows6400 := ⟨n, hn⟩
    have hp := score6400PolynomialLocatorRelationPair_inr_coeff q i
    have hs := score6400LocatorRelationPair_inr_coeff
      (fun k ↦ (q k).eval z) i
    rw [degreeLTEquiv_apply_eq_coeff] at hp hs
    simp only [i] at hp hs
    rw [hp, hs]
    rfl
  · have hnle : locatorFrobeniusRows6400 ≤ n := Nat.le_of_not_gt hn
    have hpzero :
        (score6400PolynomialLocatorRelationPair q).2.1.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        ((Polynomial.mem_degreeLT.mp
          (score6400PolynomialLocatorRelationPair q).2.2).trans_le
            (WithBot.coe_le_coe.mpr hnle))
    have hszero :
        (score6400LocatorRelationPair
          (fun k ↦ (q k).eval z)).2.1.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        ((Polynomial.mem_degreeLT.mp
          (score6400LocatorRelationPair
            (fun k ↦ (q k).eval z)).2.2).trans_le
              (WithBot.coe_le_coe.mpr hnle))
    simp only [hpzero, hszero, map_zero]

/-- The coordinate challenge-degree cap transfers to every coefficient of
the ordinary multiplier. -/
theorem score6400PolynomialLocatorRelationPair_fst_coeff_natDegree_le
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) (S n : ℕ)
    (hq : ∀ i, (q i).natDegree ≤ S) :
    ((score6400PolynomialLocatorRelationPair q).1.1.coeff n).natDegree ≤
      S := by
  by_cases hn : n < locatorOrdinaryRows6400
  · let i : Fin locatorOrdinaryRows6400 := ⟨n, hn⟩
    have hp := score6400PolynomialLocatorRelationPair_inl_coeff q i
    rw [degreeLTEquiv_apply_eq_coeff] at hp
    simp only [i] at hp
    rw [hp]
    exact hq _
  · have hnle : locatorOrdinaryRows6400 ≤ n := Nat.le_of_not_gt hn
    rw [Polynomial.coeff_eq_zero_of_degree_lt
      ((Polynomial.mem_degreeLT.mp
        (score6400PolynomialLocatorRelationPair q).1.2).trans_le
          (WithBot.coe_le_coe.mpr hnle))]
    exact Nat.zero_le S

/-- The coordinate challenge-degree cap transfers to every coefficient of
the Frobenius multiplier. -/
theorem score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) (S n : ℕ)
    (hq : ∀ i, (q i).natDegree ≤ S) :
    ((score6400PolynomialLocatorRelationPair q).2.1.coeff n).natDegree ≤
      S := by
  by_cases hn : n < locatorFrobeniusRows6400
  · let i : Fin locatorFrobeniusRows6400 := ⟨n, hn⟩
    have hp := score6400PolynomialLocatorRelationPair_inr_coeff q i
    rw [degreeLTEquiv_apply_eq_coeff] at hp
    simp only [i] at hp
    rw [hp]
    exact hq _
  · have hnle : locatorFrobeniusRows6400 ≤ n := Nat.le_of_not_gt hn
    rw [Polynomial.coeff_eq_zero_of_degree_lt
      ((Polynomial.mem_degreeLT.mp
        (score6400PolynomialLocatorRelationPair q).2.2).trans_le
          (WithBot.coe_le_coe.mpr hnle))]
    exact Nat.zero_le S

/-- The abstract maximal-minor theorem instantiated for the concrete
production locator matrix.  Besides rational spanning, every selected Cramer
vector is returned as an honest polynomial kernel identity, so it may be
specialized at every bad slope. -/
theorem exists_score6400_spanning_bounded_locatorCramerFamily
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L) :
    ∃ r : ℕ,
      ∃ rows cols : Fin r → Score6400LocatorMinorIndex,
      ∃ hrows : Function.Injective rows,
      ∃ hcols : Function.Injective cols,
        r + L = Fintype.card Score6400LocatorMinorIndex ∧
        Nat.card (SelectedColumnComplement cols) = L ∧
        (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X]))
            (selectedPolynomialPivotBlock
              (score6400LocatorPolynomialMatrix f₀ f₁)
              rows cols).det ≠ 0 ∧
        (∀ j : SelectedColumnComplement cols,
          selectedPolynomialCramerKernelVector
              (score6400LocatorPolynomialMatrix f₀ f₁)
              rows cols hcols j ∈
            LinearMap.ker
              (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin) ∧
        (∀ (j : SelectedColumnComplement cols)
            (n : Score6400LocatorMinorIndex),
          (selectedPolynomialCramerKernelVector
            (score6400LocatorPolynomialMatrix f₀ f₁)
            rows cols hcols j n).natDegree ≤ r * 2130706433) ∧
        Submodule.span (FractionRing IRSProfile.Field[X])
            (Set.range
              (mappedSelectedPolynomialCramerKernelVector
                (algebraMap IRSProfile.Field[X]
                  (FractionRing IRSProfile.Field[X]))
                (score6400LocatorPolynomialMatrix f₀ f₁)
                rows cols hcols)) =
          LinearMap.ker
            ((score6400LocatorPolynomialMatrix f₀ f₁).map
              (algebraMap IRSProfile.Field[X]
                (FractionRing IRSProfile.Field[X]))).mulVecLin := by
  classical
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  have hkernelRank' : Module.finrank K
      (LinearMap.ker (M.map ι).mulVecLin) = L := by
    simpa [K, ι, M] using hkernelRank
  obtain ⟨r, rows, cols, hrows, hcols, hrank, hcomplement,
      hdet, hspan, hdegree⟩ :=
    exists_spanning_bounded_polynomialCramerKernelFamily
      ι M L 2130706433 hkernelRank'
        (by
          intro i j
          exact score6400LocatorPolynomialMatrix_entry_natDegree_le
            f₀ f₁ i j)
  have hfullRank : Module.finrank K
      (LinearMap.ker (M.map ι).mulVecLin) =
        Nat.card (SelectedColumnComplement cols) := by
    exact hkernelRank'.trans hcomplement.symm
  have hpolynomialKer : ∀ j : SelectedColumnComplement cols,
      selectedPolynomialCramerKernelVector M rows cols hcols j ∈
        LinearMap.ker M.mulVecLin := by
    intro j
    exact selectedPolynomialCramerKernelVector_mem_full_ker_of_injective
      ι (IsFractionRing.injective IRSProfile.Field[X] K)
      M rows cols hcols hdet hfullRank j
  refine ⟨r, rows, cols, hrows, hcols, hrank, hcomplement, ?_, ?_, ?_, ?_⟩
  · simpa [K, ι, M] using hdet
  · simpa [M] using hpolynomialKer
  · simpa [M] using hdegree
  · simpa [K, ι, M] using hspan

end ProximityPrize.SubmissionLower

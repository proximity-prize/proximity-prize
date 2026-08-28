import ProximityPrize.SubmissionLower.BCHKSFrobeniusPencilMinors6400
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Expand

/-!
# Bivariate separation for the concrete Frobenius pencil

The concrete sparse Reed--Solomon kernel has both blocks moving with the
challenge: the source block is affine in `z`, while its Frobenius-conjugate
block is affine in `z ^ p`.  Treat those two parameters as independent
variables.  A maximal minor has source degree at most `h < p`; consequently
Kronecker substitution `(Z,W) = (X,X^p)` is injective on these minors.

This is the missing bridge from many concrete diagonal kernels to the
one-sided affine pencil used by the checked rational-scroll construction.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped BigOperators Polynomial.Bivariate

variable {K : Type} [Field K]

/-- Substitute the coefficient variable by `X^p` and the outer variable by
`X`.  On bivariate polynomials this is the Kronecker substitution
`(Z,W) = (X,X^p)`. -/
noncomputable def frobeniusDiagonalSubstitution (p : ℕ) :
    K[X][X] →+* K[X] :=
  Polynomial.eval₂RingHom (Polynomial.expand K p).toRingHom Polynomial.X

/-- Kronecker substitution can be expanded over the bounded outer degree. -/
theorem frobeniusDiagonalSubstitution_eq_sum_range
    {p : ℕ} (P : K[X][X]) (hP : P.natDegree < p) :
    frobeniusDiagonalSubstitution p P =
      ∑ i ∈ Finset.range p,
        Polynomial.expand K p (P.coeff i) * Polynomial.X ^ i := by
  rw [frobeniusDiagonalSubstitution]
  exact Polynomial.eval₂_eq_sum_range' _ hP Polynomial.X

/-- Exponents below `p` are the low base-`p` digit, so Kronecker
substitution preserves every coefficient in that digit class. -/
theorem coeff_frobeniusDiagonalSubstitution
    {p : ℕ} (hp : 0 < p) (P : K[X][X]) (hP : P.natDegree < p)
    (a d : ℕ) (ha : a < p) :
    (frobeniusDiagonalSubstitution p P).coeff (p * d + a) =
      (P.coeff a).coeff d := by
  rw [frobeniusDiagonalSubstitution_eq_sum_range P hP,
    Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single a]
  · rw [Polynomial.coeff_mul_X_pow]
    simpa only [Nat.mul_comm] using
      Polynomial.coeff_expand_mul hp (P.coeff a) d
  · intro i hi hia
    have hi : i < p := Finset.mem_range.mp hi
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs with hiN
    · rw [Polynomial.coeff_expand hp]
      split_ifs with hdiv
      · exfalso
        have himod : i ≡ p * d + a [MOD p] :=
          (Nat.modEq_iff_dvd' hiN).2 hdiv
        have hNmod : p * d + a ≡ a [MOD p] :=
          Nat.ModEq.modulus_mul_add
        have hiamod : i ≡ a [MOD p] := himod.trans hNmod
        unfold Nat.ModEq at hiamod
        rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt ha] at hiamod
        exact hia hiamod
      · rfl
    · rfl
  · exact fun hnot ↦ (hnot (Finset.mem_range.mpr ha)).elim

/-- A bivariate polynomial of outer degree below `p` is determined by its
restriction to the Frobenius graph `W=Z^p`. -/
theorem frobeniusDiagonalSubstitution_injective_of_natDegree_lt
    {p : ℕ} (hp : 0 < p) (P : K[X][X]) (hP : P.natDegree < p)
    (hzero : frobeniusDiagonalSubstitution p P = 0) :
    P = 0 := by
  by_contra hPzero
  let a := P.natDegree
  let d := (P.coeff a).natDegree
  have ha : a < p := hP
  have hlead : P.coeff a ≠ 0 := by
    simpa only [a, Polynomial.coeff_natDegree] using
      Polynomial.leadingCoeff_ne_zero.mpr hPzero
  have hcoeff : (P.coeff a).coeff d ≠ 0 := by
    simpa only [d, Polynomial.coeff_natDegree] using
      Polynomial.leadingCoeff_ne_zero.mpr hlead
  have hdiagCoeff := congrArg
    (fun Q : K[X] ↦ Q.coeff (p * d + a)) hzero
  rw [coeff_frobeniusDiagonalSubstitution hp P hP a d ha,
    Polynomial.coeff_zero] at hdiagCoeff
  exact hcoeff hdiagCoeff

/-- A square polynomial pencil in which the left block is affine in the
outer variable. -/
noncomputable def leftColumnPencil
    {R I J : Type} [CommRing R] [Fintype I] [Fintype J]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) R) :
    Matrix (I ⊕ J) (I ⊕ J) R[X]
  | r, Sum.inl i => Polynomial.C (base r (Sum.inl i)) +
      Polynomial.X * Polynomial.C (slope r (Sum.inl i))
  | r, Sum.inr j => Polynomial.C (base r (Sum.inr j))

/-- A determinant with only the left block affine has degree at most the
number of left columns. -/
theorem natDegree_det_leftColumnPencil_le
    {R I J : Type} [CommRing R] [Fintype I] [Fintype J]
    [DecidableEq (I ⊕ J)]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) R) :
    (leftColumnPencil base slope).det.natDegree ≤ Fintype.card I := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma hsigma
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  rw [Fintype.prod_sum_type]
  refine Polynomial.natDegree_mul_le.trans ?_
  have hleft :
      (∏ i : I,
        leftColumnPencil base slope
          (sigma (Sum.inl i)) (Sum.inl i)).natDegree ≤
        Fintype.card I := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    calc
      (∑ i : I, (leftColumnPencil base slope
          (sigma (Sum.inl i)) (Sum.inl i)).natDegree) ≤
          ∑ _i : I, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [leftColumnPencil]
            compute_degree
      _ = Fintype.card I := by simp
  have hright :
      (∏ j : J,
        leftColumnPencil base slope
          (sigma (Sum.inr j)) (Sum.inr j)).natDegree ≤ 0 := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    simp [leftColumnPencil]
  omega

/-- Two independent affine column blocks.  The source/left parameter is the
outer polynomial variable; the target/right parameter is the coefficient
polynomial variable. -/
noncomputable def twoBlockBivariatePencil
    {I J : Type} [Fintype I] [Fintype J]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    Matrix (I ⊕ J) (I ⊕ J) K[X][X] :=
  leftColumnPencil
    (fun r c ↦ match c with
      | Sum.inl i => Polynomial.C (base r (Sum.inl i))
      | Sum.inr j => Polynomial.C (base r (Sum.inr j)) +
          Polynomial.X * Polynomial.C (slope r (Sum.inr j)))
    (fun r c ↦ match c with
      | Sum.inl i => Polynomial.C (slope r (Sum.inl i))
      | Sum.inr _ => 0)

/-- The bivariate two-block pencil inherits the sharp outer/source degree
bound from `leftColumnPencil`. -/
theorem natDegree_det_twoBlockBivariatePencil_le
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    (twoBlockBivariatePencil base slope).det.natDegree ≤
      Fintype.card I := by
  unfold twoBlockBivariatePencil
  exact natDegree_det_leftColumnPencil_le _ _

/-- Diagonalizing the two independent parameters gives degrees `1` and `p`
in the two respective column blocks. -/
noncomputable def twoBlockFrobeniusPencil
    {I J : Type} [Fintype I] [Fintype J]
    (p : ℕ) (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    Matrix (I ⊕ J) (I ⊕ J) K[X]
  | r, Sum.inl i => Polynomial.C (base r (Sum.inl i)) +
      Polynomial.X * Polynomial.C (slope r (Sum.inl i))
  | r, Sum.inr j => Polynomial.C (base r (Sum.inr j)) +
      Polynomial.X ^ p * Polynomial.C (slope r (Sum.inr j))

/-- Kronecker substitution commutes with the determinant of the bivariate
two-block pencil. -/
theorem frobeniusDiagonalSubstitution_det_twoBlockBivariatePencil
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (p : ℕ) (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    frobeniusDiagonalSubstitution p
        (twoBlockBivariatePencil base slope).det =
      (twoBlockFrobeniusPencil p base slope).det := by
  classical
  rw [RingHom.map_det]
  congr 1
  ext r c
  cases c <;>
    simp [frobeniusDiagonalSubstitution, twoBlockBivariatePencil,
      twoBlockFrobeniusPencil, leftColumnPencil]

/-- The diagonal determinant degree is at most
`#left + p * #right`. -/
theorem natDegree_det_twoBlockFrobeniusPencil_le
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (p : ℕ) (base slope : Matrix (I ⊕ J) (I ⊕ J) K) :
    (twoBlockFrobeniusPencil p base slope).det.natDegree ≤
      Fintype.card I + p * Fintype.card J := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma hsigma
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  rw [Fintype.prod_sum_type]
  refine Polynomial.natDegree_mul_le.trans ?_
  have hleft :
      (∏ i : I,
        twoBlockFrobeniusPencil p base slope
          (sigma (Sum.inl i)) (Sum.inl i)).natDegree ≤
        Fintype.card I := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    calc
      (∑ i : I, (twoBlockFrobeniusPencil p base slope
          (sigma (Sum.inl i)) (Sum.inl i)).natDegree) ≤
          ∑ _i : I, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [twoBlockFrobeniusPencil]
            compute_degree
      _ = Fintype.card I := by simp
  have hright :
      (∏ j : J,
        twoBlockFrobeniusPencil p base slope
          (sigma (Sum.inr j)) (Sum.inr j)).natDegree ≤
        p * Fintype.card J := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    calc
      (∑ j : J, (twoBlockFrobeniusPencil p base slope
          (sigma (Sum.inr j)) (Sum.inr j)).natDegree) ≤
          ∑ _j : J, p := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [twoBlockFrobeniusPencil]
            compute_degree
      _ = p * Fintype.card J := by simp [Nat.mul_comm]
  omega

/-- Evaluating the two independent variables specializes the two column
blocks independently. -/
def twoBlockSpecialization
    {I J : Type} [Fintype I] [Fintype J]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) (z w : K) :
    Matrix (I ⊕ J) (I ⊕ J) K
  | r, Sum.inl i => base r (Sum.inl i) + z * slope r (Sum.inl i)
  | r, Sum.inr j => base r (Sum.inr j) + w * slope r (Sum.inr j)

theorem evalEval_det_twoBlockBivariatePencil
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K) (z w : K) :
    Polynomial.evalEvalRingHom w z
        (twoBlockBivariatePencil base slope).det =
      (twoBlockSpecialization base slope z w).det := by
  classical
  rw [RingHom.map_det]
  congr 1
  ext r c
  cases c <;>
    simp [twoBlockBivariatePencil, leftColumnPencil,
      twoBlockSpecialization] <;> ring

/-- Point evaluation after Kronecker substitution is bivariate evaluation on
the Frobenius graph. -/
theorem eval_frobeniusDiagonalSubstitution
    (p : ℕ) (P : K[X][X]) (z : K) :
    (frobeniusDiagonalSubstitution p P).eval z =
      P.evalEval (z ^ p) z := by
  have hcomp :
      (Polynomial.evalRingHom z).comp
          (Polynomial.expand K p).toRingHom =
        Polynomial.evalRingHom (z ^ p) := by
    ext <;> simp
  change (Polynomial.evalRingHom z)
      (Polynomial.eval₂
        (Polynomial.expand K p).toRingHom Polynomial.X P) = _
  rw [Polynomial.hom_eval₂, hcomp]
  have hx : (Polynomial.evalRingHom z) (Polynomial.X : K[X]) = z := by
    simp
  rw [hx, Polynomial.eval₂_eq_eval_map]
  exact Polynomial.map_evalRingHom_eval (z ^ p) z P

/-- The selected bivariate maximal minor of a low stack. -/
noncomputable def lowStackBivariateMinor
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) : K[X][X] :=
  (twoBlockBivariatePencil
    ((lowStackMatrix S source₀ target₀ h).submatrix e id)
    ((lowStackMatrix S source₁ target₁ h).submatrix e id)).det

/-- The selected diagonal Frobenius minor. -/
noncomputable def lowStackFrobeniusMinor
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K)
    (h p : ℕ) (e : LowStackIndex h → S) : K[X] :=
  (twoBlockFrobeniusPencil p
    ((lowStackMatrix S source₀ target₀ h).submatrix e id)
    ((lowStackMatrix S source₁ target₁ h).submatrix e id)).det

/-- A selected bivariate low-stack minor has source-parameter degree at most
`h`. -/
theorem lowStackBivariateMinor_natDegree_le
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) :
    (lowStackBivariateMinor S source₀ source₁ target₀ target₁ h e).natDegree ≤ h := by
  simpa only [lowStackBivariateMinor, Fintype.card_fin] using
    natDegree_det_twoBlockBivariatePencil_le
      ((lowStackMatrix S source₀ target₀ h).submatrix e id)
      ((lowStackMatrix S source₁ target₁ h).submatrix e id)

/-- Diagonalizing the two parameters commutes with the selected minor. -/
theorem lowStackFrobeniusMinor_eq_diagonal
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K)
    (h p : ℕ) (e : LowStackIndex h → S) :
    lowStackFrobeniusMinor S source₀ source₁ target₀ target₁ h p e =
      frobeniusDiagonalSubstitution p
        (lowStackBivariateMinor S source₀ source₁ target₀ target₁ h e) := by
  exact (frobeniusDiagonalSubstitution_det_twoBlockBivariatePencil
    p
    ((lowStackMatrix S source₀ target₀ h).submatrix e id)
    ((lowStackMatrix S source₁ target₁ h).submatrix e id)).symm

/-- The diagonal minor has challenge degree at most `h + p*h`. -/
theorem lowStackFrobeniusMinor_natDegree_le
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K)
    (h p : ℕ) (e : LowStackIndex h → S) :
    (lowStackFrobeniusMinor S source₀ source₁ target₀ target₁ h p e).natDegree ≤
      h + p * h := by
  simpa only [lowStackFrobeniusMinor, Fintype.card_fin] using
    natDegree_det_twoBlockFrobeniusPencil_le p
      ((lowStackMatrix S source₀ target₀ h).submatrix e id)
      ((lowStackMatrix S source₁ target₁ h).submatrix e id)

/-- Independent bivariate specialization is the expected low-stack minor. -/
theorem lowStackBivariateMinor_evalEval
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K) (h : ℕ)
    (e : LowStackIndex h → S) (z w : K) :
    (lowStackBivariateMinor S source₀ source₁ target₀ target₁ h e).evalEval w z =
      ((lowStackMatrix S
        (fun x ↦ source₀ x + z * source₁ x)
        (fun x ↦ target₀ x + w * target₁ x) h).submatrix e id).det := by
  rw [lowStackBivariateMinor,
    ← Polynomial.coe_evalEvalRingHom,
    evalEval_det_twoBlockBivariatePencil]
  congr 1
  ext r c
  cases c <;>
    simp [twoBlockSpecialization, lowStackMatrix] <;> ring

/-- Diagonal specialization is the concrete Frobenius low-stack minor. -/
theorem lowStackFrobeniusMinor_eval
    (S : Finset K) (source₀ source₁ target₀ target₁ : K → K)
    (h p : ℕ) (e : LowStackIndex h → S) (z : K) :
    (lowStackFrobeniusMinor S source₀ source₁ target₀ target₁ h p e).eval z =
      ((lowStackMatrix S
        (fun x ↦ source₀ x + z * source₁ x)
        (fun x ↦ target₀ x + z ^ p * target₁ x) h).submatrix e id).det := by
  rw [lowStackFrobeniusMinor_eq_diagonal,
    eval_frobeniusDiagonalSubstitution,
    lowStackBivariateMinor_evalEval]

/-- More roots than the diagonal degree force a selected bivariate minor to
vanish identically.  The strict inequality `h<p` is exactly what makes the
Kronecker substitution injective. -/
theorem lowStackBivariateMinor_eq_zero_of_many_frobenius_kernels
    (S T : Finset K) (source₀ source₁ target₀ target₁ : K → K)
    (h p : ℕ) (e : LowStackIndex h → S)
    (hp : 0 < p) (hhp : h < p) (hcard : h + p * h < T.card)
    (hkernels : ∀ z ∈ T,
      LinearMap.ker (lowStackRelationMap S
        (fun x ↦ source₀ x + z * source₁ x)
        (fun x ↦ target₀ x + z ^ p * target₁ x) h) ≠ ⊥) :
    lowStackBivariateMinor S source₀ source₁ target₀ target₁ h e = 0 := by
  apply frobeniusDiagonalSubstitution_injective_of_natDegree_lt hp
  · exact (lowStackBivariateMinor_natDegree_le
      S source₀ source₁ target₀ target₁ h e).trans_lt hhp
  · rw [← lowStackFrobeniusMinor_eq_diagonal]
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (lowStackFrobeniusMinor S source₀ source₁ target₀ target₁ h p e) T
    · intro z hz
      rw [lowStackFrobeniusMinor_eval]
      exact all_lowStack_maximal_minors_zero_of_ker_ne_bot
        S (fun x ↦ source₀ x + z * source₁ x)
        (fun x ↦ target₀ x + z ^ p * target₁ x) h
        (hkernels z hz) e
    · exact (lowStackFrobeniusMinor_natDegree_le
        S source₀ source₁ target₀ target₁ h p e).trans_lt hcard

/-- Many concrete kernels on the Frobenius graph force every independent
two-parameter specialization to have a nontrivial low-stack kernel. -/
theorem lowStack_kernel_of_many_frobenius_kernels
    (S T : Finset K) (source₀ source₁ target₀ target₁ : K → K)
    (h p : ℕ)
    (hp : 0 < p) (hhp : h < p) (hcard : h + p * h < T.card)
    (hkernels : ∀ z ∈ T,
      LinearMap.ker (lowStackRelationMap S
        (fun x ↦ source₀ x + z * source₁ x)
        (fun x ↦ target₀ x + z ^ p * target₁ x) h) ≠ ⊥)
    (z w : K) :
    LinearMap.ker (lowStackRelationMap S
      (fun x ↦ source₀ x + z * source₁ x)
      (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥ := by
  apply lowStackRelationMap_ker_ne_bot_of_all_maximal_minors_zero
  intro e he
  rw [← lowStackBivariateMinor_evalEval
    S source₀ source₁ target₀ target₁ h e z w]
  rw [lowStackBivariateMinor_eq_zero_of_many_frobenius_kernels
    S T source₀ source₁ target₀ target₁ h p e hp hhp hcard hkernels]
  exact Polynomial.evalEval_zero w z

end ProximityPrize.SubmissionLower

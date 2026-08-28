import ProximityPrize.SubmissionLower.BCHKSAlgebraLagrangeInterpolation6400
import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialCramerFamily6400
import ProximityPrize.SubmissionLower.BCHKSLocatorPairToCode6400

/-!
# The bivariate affine code component of a polynomial locator family

A Cramer kernel vector has polynomial coordinates in the affine challenge.
This module retains that challenge variable while interpolating its received-
word relation in the locator variable.  The resulting bivariate polynomial
specializes to `score6400LocatorPairToCode` at every challenge.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark

/-- The affine received symbol at one coordinate, as a polynomial in the
challenge. -/
noncomputable def score6400ReceivedPolynomial
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) : IRSProfile.Field[X] :=
  Polynomial.C (f₀ i) + Polynomial.X * Polynomial.C (f₁ i)

@[simp]
theorem score6400ReceivedPolynomial_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) (z : IRSProfile.Field) :
    (score6400ReceivedPolynomial f₀ f₁ i).eval z =
      f₀ i + z * f₁ i := by
  simp only [score6400ReceivedPolynomial, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]

noncomputable def affinePowerPolynomial
    {F : Type} [Field F] (p : ℕ) (a b : F) : F[X] :=
  Polynomial.C a + Polynomial.X ^ p * Polynomial.C b

theorem affinePowerPolynomial_eval
    {F : Type} [Field F] (p : ℕ) (a b z : F) :
    (affinePowerPolynomial p a b).eval z =
      a + z ^ p * b := by
  simp only [affinePowerPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

theorem affinePowerPolynomial_natDegree_le
    {F : Type} [Field F] (p : ℕ) (a b : F) :
    (affinePowerPolynomial p a b).natDegree ≤ p := by
  simp only [affinePowerPolynomial]
  compute_degree

theorem score6400ReceivedPolynomial_natDegree_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    (score6400ReceivedPolynomial f₀ f₁ i).natDegree ≤ 1 := by
  simp only [score6400ReceivedPolynomial]
  compute_degree

/-- The Frobenius of the affine received symbol, kept in its sparse
characteristic-`p` form so elaboration never expands a billionth power. -/
noncomputable def score6400FrobeniusReceivedPolynomial
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) : IRSProfile.Field[X] :=
  affinePowerPolynomial 2130706433
    (koalaSexticFrobenius (f₀ i))
    (koalaSexticFrobenius (f₁ i))

theorem score6400FrobeniusReceivedPolynomial_natDegree_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i).natDegree ≤
      2130706433 := by
  exact affinePowerPolynomial_natDegree_le 2130706433 _ _

theorem score6400FrobeniusReceivedPolynomial_eval_explicit
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) (z : IRSProfile.Field) :
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i).eval z =
      koalaSexticFrobenius (f₀ i) +
        z ^ 2130706433 * koalaSexticFrobenius (f₁ i) := by
  exact affinePowerPolynomial_eval 2130706433
    (koalaSexticFrobenius (f₀ i))
    (koalaSexticFrobenius (f₁ i)) z

@[simp]
theorem score6400FrobeniusReceivedPolynomial_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) (z : IRSProfile.Field) :
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i).eval z =
      koalaSexticFrobenius (f₀ i + z * f₁ i) := by
  rw [score6400FrobeniusReceivedPolynomial_eval_explicit,
    map_add, map_mul, locator_koalaSexticFrobenius_apply z]

theorem score6400PolynomialLocatorRelationPair_fst_eval_eval
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (x z : IRSProfile.Field) :
    ((score6400PolynomialLocatorRelationPair q).1.1.eval
      (Polynomial.C x)).eval z =
      (score6400LocatorRelationPair (fun k => (q k).eval z)).1.1.eval x := by
  have h := (Polynomial.eval_map_apply
    (p := (score6400PolynomialLocatorRelationPair q).1.1)
    (f := Polynomial.evalRingHom z) (Polynomial.C x)).symm
  rw [score6400PolynomialLocatorRelationPair_fst_map_eval] at h
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using h

theorem score6400PolynomialLocatorRelationPair_snd_eval_eval
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (x z : IRSProfile.Field) :
    ((score6400PolynomialLocatorRelationPair q).2.1.eval
      (Polynomial.C x)).eval z =
      (score6400LocatorRelationPair (fun k => (q k).eval z)).2.1.eval x := by
  have h := (Polynomial.eval_map_apply
    (p := (score6400PolynomialLocatorRelationPair q).2.1)
    (f := Polynomial.evalRingHom z) (Polynomial.C x)).symm
  rw [score6400PolynomialLocatorRelationPair_snd_map_eval] at h
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using h

noncomputable def polynomialBilinearWord
    {F : Type} [Field F] (A B R S : F[X]) : F[X] :=
  A * R + B * S

theorem polynomialBilinearWord_eval
    {F : Type} [Field F] (A B R S : F[X]) (z : F) :
    (polynomialBilinearWord A B R S).eval z =
      A.eval z * R.eval z + B.eval z * S.eval z := by
  simp only [polynomialBilinearWord, Polynomial.eval_add,
    Polynomial.eval_mul]

theorem polynomialBilinearWord_natDegree_le
    {F : Type} [Field F] (A B R S : F[X]) (D p : ℕ)
    (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (hR : R.natDegree ≤ p) (hS : S.natDegree ≤ p) :
    (polynomialBilinearWord A B R S).natDegree ≤ D + p := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hA hR)
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hB hS)

/-- The polynomial-valued relation word attached to a polynomial locator
pair.  Its second received symbol is raised to the sextic Frobenius power. -/
noncomputable def score6400PolynomialPairRelationWord
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : IRSProfile.Index) : IRSProfile.Field[X] :=
  polynomialBilinearWord
    ((score6400PolynomialLocatorRelationPair q).1.1.eval
      (Polynomial.C (IRSProfile.domain i)))
    ((score6400PolynomialLocatorRelationPair q).2.1.eval
      (Polynomial.C (IRSProfile.domain i)))
    (score6400ReceivedPolynomial f₀ f₁ i)
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i)

theorem score6400PolynomialPairRelationWord_natDegree_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (D : ℕ) (hq : ∀ k, (q k).natDegree ≤ D)
    (i : IRSProfile.Index) :
    (score6400PolynomialPairRelationWord f₀ f₁ q i).natDegree ≤
      D + 2130706433 := by
  rw [score6400PolynomialPairRelationWord]
  apply polynomialBilinearWord_natDegree_le _ _ _ _ D 2130706433
  · apply eval_C_natDegree_le_of_coeff_natDegree_le
    intro n
    exact score6400PolynomialLocatorRelationPair_fst_coeff_natDegree_le
      q D n hq
  · apply eval_C_natDegree_le_of_coeff_natDegree_le
    intro n
    exact score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
      q D n hq
  · exact (score6400ReceivedPolynomial_natDegree_le f₀ f₁ i).trans
      (by norm_num)
  · exact score6400FrobeniusReceivedPolynomial_natDegree_le f₀ f₁ i

/-- Specializing the challenge in the polynomial relation word gives the
existing concrete locator relation. -/
theorem score6400PolynomialPairRelationWord_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : IRSProfile.Index) (z : IRSProfile.Field) :
    (score6400PolynomialPairRelationWord f₀ f₁ q i).eval z =
      (score6400LocatorRelationPair (fun k => (q k).eval z)).1.1.eval
            (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
        (score6400LocatorRelationPair (fun k => (q k).eval z)).2.1.eval
            (IRSProfile.domain i) *
          koalaSexticFrobenius (f₀ i + z * f₁ i) := by
  rw [score6400PolynomialPairRelationWord]
  rw [polynomialBilinearWord_eval]
  rw [score6400FrobeniusReceivedPolynomial_eval]
  rw [score6400ReceivedPolynomial_eval]
  rw [score6400PolynomialLocatorRelationPair_fst_eval_eval]
  rw [score6400PolynomialLocatorRelationPair_snd_eval_eval]

/-- A polynomial kernel identity makes every required polynomial-valued
syndrome moment vanish.  Equality is checked at every field challenge; the
challenge-degree cap makes those evaluations determining. -/
theorem score6400PolynomialPairRelationMoment_eq_zero
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (D : ℕ) (hqdegree : ∀ k, (q k).natDegree ≤ D)
    (hfield : D + 2130706433 < Fintype.card IRSProfile.Field)
    (t : ℕ) (ht : t < locatorColumns6400) :
    polynomialSyndromeMoment IRSProfile.domain
      (score6400PolynomialPairRelationWord f₀ f₁ q) t = 0 := by
  let M := polynomialSyndromeMoment IRSProfile.domain
    (score6400PolynomialPairRelationWord f₀ f₁ q) t
  change M = 0
  have heval : ∀ z : IRSProfile.Field, M.eval z = 0 := by
    intro z
    dsimp only [M]
    rw [polynomialSyndromeMoment_eval]
    have hqz := score6400_eval_mem_locatorKernel_of_polynomial_mem_ker
      f₀ f₁ q hqker z
    simpa only [score6400PolynomialPairRelationWord_eval] using
      (score6400_locatorKernel_received_relation_moment
        f₀ f₁ z (fun k => (q k).eval z) hqz t ht)
  have hword : ∀ i : IRSProfile.Index,
      (score6400PolynomialPairRelationWord f₀ f₁ q i).natDegree ≤
        D + 2130706433 := by
    intro i
    exact score6400PolynomialPairRelationWord_natDegree_le
      f₀ f₁ q D hqdegree i
  have hmomentDegree : M.natDegree ≤ D + 2130706433 := by
    dsimp only [M]
    exact polynomialSyndromeMoment_natDegree_le
      IRSProfile.domain
      (score6400PolynomialPairRelationWord f₀ f₁ q) t
      (D + 2130706433) hword
  have hdegree : M.natDegree < Fintype.card IRSProfile.Field :=
    hmomentDegree.trans_lt hfield
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    M Function.injective_id heval hdegree

/-- Interpolate the polynomial relation word in the locator variable while
retaining the affine challenge as its coefficient variable. -/
noncomputable def score6400PolynomialLocatorPairToCode
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) :
    IRSProfile.Field[X][X] :=
  algebraLagrangeInterpolate Finset.univ
    (fun i : IRSProfile.Index => IRSProfile.domain i)
    (score6400PolynomialPairRelationWord f₀ f₁ q)

theorem score6400PolynomialLocatorPairToCode_eq_interpolate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X]) :
    score6400PolynomialLocatorPairToCode f₀ f₁ q =
      algebraLagrangeInterpolate Finset.univ
        (fun i : IRSProfile.Index => IRSProfile.domain i)
        (score6400PolynomialPairRelationWord f₀ f₁ q) := rfl

theorem score6400PolynomialLocatorPairToCode_coeff_natDegree_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (D : ℕ) (hq : ∀ k, (q k).natDegree ≤ D) (n : ℕ) :
    ((score6400PolynomialLocatorPairToCode f₀ f₁ q).coeff n).natDegree ≤
      D + 2130706433 := by
  exact algebraLagrangeInterpolate_coeff_natDegree_le
    Finset.univ (fun i : IRSProfile.Index => IRSProfile.domain i)
    (score6400PolynomialPairRelationWord f₀ f₁ q)
    (D + 2130706433) n
    (fun i hi => score6400PolynomialPairRelationWord_natDegree_le
      f₀ f₁ q D hq i)

/-- The polynomial-valued locator relation has the same `185363` locator-
degree cap as every concrete specialization. -/
theorem score6400PolynomialLocatorPairToCode_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (D : ℕ) (hqdegree : ∀ k, (q k).natDegree ≤ D)
    (hfield : D + 2130706433 < Fintype.card IRSProfile.Field) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q).natDegree <
      185363 := by
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hcolumns : locatorColumns6400 = 76781 := by
    norm_num [locatorColumns6400]
  have hraw :=
    algebraLagrangeInterpolate_natDegree_lt_card_sub_of_zero_prefix
      IRSProfile.domain
      (score6400PolynomialPairRelationWord f₀ f₁ q)
      locatorColumns6400
      (by rw [hcard, hcolumns]; norm_num)
      (fun t ht => score6400PolynomialPairRelationMoment_eq_zero
        f₀ f₁ q hqker D hqdegree hfield t ht)
  rw [hcard, hcolumns] at hraw
  simpa only [score6400PolynomialLocatorPairToCode] using hraw

@[simp]
theorem score6400PolynomialLocatorPairToCode_eval_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : IRSProfile.Index) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q).eval
        (Polynomial.C (IRSProfile.domain i)) =
      score6400PolynomialPairRelationWord f₀ f₁ q i := by
  exact algebraLagrangeInterpolate_eval_at_node
    Finset.univ (fun j : IRSProfile.Index => IRSProfile.domain j)
    (score6400PolynomialPairRelationWord f₀ f₁ q)
    IRSProfile.domain.injective.injOn (Finset.mem_univ i)

end ProximityPrize.SubmissionLower

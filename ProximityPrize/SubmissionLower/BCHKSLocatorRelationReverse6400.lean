import ProximityPrize.SubmissionLower.BCHKSLocatorRelationProduction6400

/-!
# Pointwise relations return to the production locator kernel

The production development already proves that a specialized locator-kernel
vector gives a pointwise homogeneous relation for every nearby decoded word.
This file proves the converse needed for local-nullity arguments: any pair of
polynomials inside the two production degree caps which satisfies that
pointwise error relation is itself a vector in the specialized locator
kernel.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A degree-capped pointwise semilinear error relation has all production
syndrome moments zero, hence its coefficient vector lies in the specialized
locator kernel. -/
theorem score6400_mem_locatorKernel_of_pointwise_error_relation
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (u : PolynomialPairSpace IRSProfile.Field locatorOrdinaryRows6400
      locatorFrobeniusRows6400)
    (P : IRSProfile.Field[X])
    (hPdegree : P.natDegree ≤ 131071)
    (hrelation : ∀ i,
      u.1.1.eval (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        u.2.1.eval (IRSProfile.domain i) *
          koalaSexticFrobenius
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) = 0) :
    mixedStackDomainEquiv locatorOrdinaryRows6400
        locatorFrobeniusRows6400 u ∈
      LinearMap.ker
        (twoBlockSpecialization
          (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
          z (z ^ 2130706433)).mulVecLin := by
  classical
  let q : Score6400LocatorMinorIndex → IRSProfile.Field :=
    mixedStackDomainEquiv locatorOrdinaryRows6400
      locatorFrobeniusRows6400 u
  let received : IRSProfile.Index → IRSProfile.Field := fun i =>
    u.1.1.eval (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
      u.2.1.eval (IRSProfile.domain i) *
        koalaSexticFrobenius (f₀ i + z * f₁ i)
  let codeword : IRSProfile.Index → IRSProfile.Field := fun i =>
    u.1.1.eval (IRSProfile.domain i) * P.eval (IRSProfile.domain i) +
      u.2.1.eval (IRSProfile.domain i) *
        koalaSexticFrobenius (P.eval (IRSProfile.domain i))
  have hreceivedCode : received = codeword := by
    funext i
    have hi := hrelation i
    simp only [map_sub] at hi
    dsimp only [received, codeword]
    linear_combination hi
  have hu₀degree : u.1.1.natDegree < locatorOrdinaryRows6400 :=
    natDegree_lt_of_mem_degreeLT_of_pos locatorOrdinaryRows6400
      (by norm_num [locatorOrdinaryRows6400]) u.1
  have hu₁degree : u.2.1.natDegree < locatorFrobeniusRows6400 :=
    natDegree_lt_of_mem_degreeLT_of_pos locatorFrobeniusRows6400
      (by norm_num [locatorFrobeniusRows6400]) u.2
  have hu₀cap : u.1.1.natDegree ≤ 54291 := by
    norm_num [locatorOrdinaryRows6400] at hu₀degree ⊢
    omega
  have hu₁cap : u.2.1.natDegree ≤ 22488 := by
    norm_num [locatorFrobeniusRows6400] at hu₁degree ⊢
    omega
  let codePolynomial : IRSProfile.Field[X] :=
    u.1.1 * P + u.2.1 * P.map koalaSexticFrobenius.toRingHom
  have hcodeDegree : ∀ t < locatorColumns6400,
      codePolynomial.natDegree + t <
        Fintype.card IRSProfile.Index - 1 := by
    intro t ht
    have hmapDegree :
        (P.map koalaSexticFrobenius.toRingHom).natDegree ≤ P.natDegree :=
      Polynomial.natDegree_map_le
    have hleft : (u.1.1 * P).natDegree ≤
        u.1.1.natDegree + P.natDegree := Polynomial.natDegree_mul_le
    have hright :
        (u.2.1 * P.map koalaSexticFrobenius.toRingHom).natDegree ≤
          u.2.1.natDegree +
            (P.map koalaSexticFrobenius.toRingHom).natDegree :=
      Polynomial.natDegree_mul_le
    have hsum : codePolynomial.natDegree ≤
        max (u.1.1 * P).natDegree
          (u.2.1 * P.map koalaSexticFrobenius.toRingHom).natDegree := by
      exact Polynomial.natDegree_add_le _ _
    have hleftCap : (u.1.1 * P).natDegree ≤ 185362 := by
      calc
        (u.1.1 * P).natDegree ≤
            u.1.1.natDegree + P.natDegree := hleft
        _ ≤ 54291 + 131071 := Nat.add_le_add hu₀cap hPdegree
        _ = 185362 := by norm_num
    have hrightCap :
        (u.2.1 * P.map koalaSexticFrobenius.toRingHom).natDegree ≤
          153559 := by
      calc
        (u.2.1 * P.map koalaSexticFrobenius.toRingHom).natDegree ≤
            u.2.1.natDegree +
              (P.map koalaSexticFrobenius.toRingHom).natDegree := hright
        _ ≤ 22488 + 131071 :=
          Nat.add_le_add hu₁cap (hmapDegree.trans hPdegree)
        _ = 153559 := by norm_num
    have hcodeCap : codePolynomial.natDegree ≤ 185362 := by
      apply hsum.trans
      exact max_le hleftCap (hrightCap.trans (by norm_num))
    norm_num [locatorColumns6400, locatorOrdinaryRows6400,
      locatorFrobeniusRows6400, IRSProfile.Index] at ht ⊢
    omega
  have hcodeMoment : ∀ t < locatorColumns6400,
      rsSyndromeMoment IRSProfile.domain codeword t = 0 := by
    intro t ht
    have hmoment := rs_barycentric_moment_eq_zero
      IRSProfile.domain codePolynomial t (hcodeDegree t ht)
    have hcodeEval : ∀ i,
        codePolynomial.eval (IRSProfile.domain i) = codeword i := by
      intro i
      simp only [codePolynomial, codeword, Polynomial.eval_add,
        Polynomial.eval_mul]
      rw [polynomial_map_eval_of_fixed_locator koalaSexticFrobenius P
        (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i)]
    simpa only [rsSyndromeMoment, hcodeEval] using hmoment
  have hreceivedMoment : ∀ t < locatorColumns6400,
      rsSyndromeMoment IRSProfile.domain received t = 0 := by
    intro t ht
    rw [hreceivedCode]
    exact hcodeMoment t ht
  change q ∈ LinearMap.ker
    (twoBlockSpecialization
      (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
      z (z ^ 2130706433)).mulVecLin
  rw [LinearMap.mem_ker]
  funext coefficient
  let t : Fin locatorColumns6400 :=
    score6400LocatorCoefficientEquiv coefficient
  have hmoment := hreceivedMoment t.1 t.2
  have hordinary := rsSyndromeMoment_eval_mul
    IRSProfile.domain (fun i => f₀ i + z * f₁ i)
    locatorOrdinaryRows6400 t.1 u.1
  have hfrobenius := rsSyndromeMoment_eval_mul
    IRSProfile.domain
    (fun i => koalaSexticFrobenius (f₀ i + z * f₁ i))
    locatorFrobeniusRows6400 t.1 u.2
  rw [rsSyndromeMoment_add, hordinary, hfrobenius] at hmoment
  have huq : score6400LocatorRelationPair q = u := by
    exact (mixedStackDomainEquiv locatorOrdinaryRows6400
      locatorFrobeniusRows6400).symm_apply_apply u
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Pi.zero_apply]
  simp_rw [score6400LocatorStack_specialize_ordinary,
    score6400LocatorStack_specialize_frobenius]
  simp_rw [map_rsSyndromeMoment IRSProfile.domain koalaSexticFrobenius
    koalaSexticFrobenius_fixed_domain]
  have hcoeffInl : ∀ i : Fin locatorOrdinaryRows6400,
      q (Sum.inl i) = Polynomial.degreeLTEquiv IRSProfile.Field
        locatorOrdinaryRows6400 u.1 i := by
    intro i
    rw [← score6400LocatorRelationPair_inl_coeff q i, huq]
  have hcoeffInr : ∀ i : Fin locatorFrobeniusRows6400,
      q (Sum.inr i) = Polynomial.degreeLTEquiv IRSProfile.Field
        locatorFrobeniusRows6400 u.2 i := by
    intro i
    rw [← score6400LocatorRelationPair_inr_coeff q i, huq]
  simp_rw [hcoeffInl, hcoeffInr]
  simpa only [t, add_comm, mul_comm] using hmoment

end ProximityPrize.SubmissionLower

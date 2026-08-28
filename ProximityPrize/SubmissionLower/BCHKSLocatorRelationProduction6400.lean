import ProximityPrize.SubmissionLower.BCHKSLocatorProductionPencil6400
import ProximityPrize.SubmissionLower.BCHKSLocatorDeterminantIncidence6400

/-!
# Producing global relations from the locator pencil

The direct locator pencil records a prefix of barycentric Reed--Solomon
syndromes.  This file begins the converse direction needed by the rank-two
branch: if a word has a zero prefix of `rows` moments and vanishes on more
than `n - rows` evaluation coordinates, then it vanishes everywhere.

At the score-64 endpoint the relation word has `76781` zero moments and at
least `185364` zero coordinates, while `262144 - 76781 = 185363`.  Thus every
polynomial-pair vector in the production pencil kernel gives a genuine
pointwise semilinear error relation, rather than merely a syndrome relation.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000

variable {K : Type} [Field K]

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- A zero prefix of barycentric moments is a complete parity check once the
word already has more than `n - rows` known zero coordinates.

The proof interpolates the word on the full evaluation domain.  Successive
moments kill its coefficients from the top down: after the first `t`
coefficients have vanished, multiplying by `X^t` remains below degree `n`,
so Lagrange's top-coefficient formula identifies the next coefficient with
the `t`-th syndrome moment. -/
theorem rsSyndromeMoment_eq_zero_of_prefix_and_many_zeros
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e : ι → K) (rows : ℕ)
    (hrows : rows ≤ Fintype.card ι)
    (hmoment : ∀ t, t < rows → rsSyndromeMoment α e t = 0)
    (A : Finset ι)
    (hAcard : Fintype.card ι - rows < A.card)
    (hzero : ∀ i ∈ A, e i = 0) :
    ∀ i, e i = 0 := by
  classical
  let Q : K[X] :=
    Lagrange.interpolate Finset.univ (fun i : ι => α i) e
  have hQeval : ∀ i, Q.eval (α i) = e i := by
    intro i
    exact Lagrange.eval_interpolate_at_node e α.injective.injOn
      (Finset.mem_univ i)
  have hQdegree : Q.degree < (Fintype.card ι : WithBot ℕ) := by
    change
      ((Lagrange.interpolate Finset.univ (fun i : ι => α i)) e).degree <
        (Fintype.card ι : WithBot ℕ)
    simpa only [Finset.card_univ] using
      (Lagrange.degree_interpolate_lt
        (s := Finset.univ) (v := fun i : ι => α i)
        e α.injective.injOn)
  by_cases hQzero : Q = 0
  · intro i
    rw [← hQeval i, hQzero, Polynomial.eval_zero]
  have hQnat : Q.natDegree < Fintype.card ι := by
    rw [Polynomial.degree_eq_natDegree hQzero] at hQdegree
    exact WithBot.coe_lt_coe.mp hQdegree
  have hnpos : 0 < Fintype.card ι := by
    have hAle : A.card ≤ Fintype.card ι := by
      simpa only [Finset.card_univ] using Finset.card_le_univ A
    omega
  have hQbound : ∀ t, t ≤ rows →
      Q.natDegree < Fintype.card ι - t := by
    intro t ht
    induction t with
    | zero => simpa using hQnat
    | succ t ih =>
        have htRows : t ≤ rows := by omega
        have hi := ih htRows
        by_contra hnext
        have htltRows : t < rows := by omega
        have hdegreeExact :
            Q.natDegree = Fintype.card ι - (t + 1) := by
          omega
        have hsum :
            Q.natDegree + t = Fintype.card ι - 1 := by
          omega
        let P : K[X] := Q * Polynomial.X ^ t
        have hPne : P ≠ 0 := by
          exact mul_ne_zero hQzero
            (pow_ne_zero t (Polynomial.X_ne_zero :
              (Polynomial.X : K[X]) ≠ 0))
        have hPnat : P.natDegree = Fintype.card ι - 1 := by
          simpa only [P, Polynomial.natDegree_mul_X_pow t hQzero] using hsum
        have hPdegree : P.degree < (Fintype.card ι : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree hPne, hPnat]
          exact WithBot.coe_lt_coe.mpr (Nat.sub_lt hnpos Nat.one_pos)
        have htop := Lagrange.coeff_eq_sum
          (s := Finset.univ) (v := fun i : ι => α i)
          α.injective.injOn hPdegree
        have htopzero : P.coeff (Fintype.card ι - 1) = 0 := by
          calc
            P.coeff (Fintype.card ι - 1) =
                rsSyndromeMoment α e t := by
              simpa [P, rsSyndromeMoment, rsBarycentricDenominator,
                hQeval, mul_comm] using htop
            _ = 0 := hmoment t htltRows
        have hleadzero : Q.leadingCoeff = 0 := by
          calc
            Q.leadingCoeff = Q.coeff Q.natDegree := rfl
            _ = (Q * Polynomial.X ^ t).coeff
                (Q.natDegree + t) :=
              (Polynomial.coeff_mul_X_pow Q t Q.natDegree).symm
            _ = P.coeff (Fintype.card ι - 1) := by rw [hsum]
            _ = 0 := htopzero
        exact (Polynomial.leadingCoeff_ne_zero.mpr hQzero) hleadzero
  have hQsmall : Q.natDegree < A.card :=
    (hQbound rows le_rfl).trans hAcard
  have hQzero' : Q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      Q (f := fun i : A => α i.1)
    · intro i j hij
      apply Subtype.ext
      exact α.injective hij
    · intro i
      rw [hQeval]
      exact hzero i.1 i.2
    · simpa only [Fintype.card_coe] using hQsmall
  exact (hQzero hQzero').elim

/-- The exact score-64 syndrome-converse arithmetic has one spare agreement
coordinate. -/
theorem score6400_relation_syndrome_converse_numeric :
    262144 - 76781 < 185364 := by
  norm_num

/-- Multiplication of a word by a degree-bounded polynomial becomes Hankel
convolution of its syndrome moments. -/
theorem rsSyndromeMoment_eval_mul
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e : ι → K) (c t : ℕ)
    (A : Polynomial.degreeLT K c) :
    rsSyndromeMoment α (fun i => A.1.eval (α i) * e i) t =
      ∑ j : Fin c,
        (Polynomial.degreeLTEquiv K c A) j *
          rsSyndromeMoment α e (t + j.1) := by
  classical
  simp only [rsSyndromeMoment]
  calc
    (∑ i : ι,
        α i ^ t * (A.1.eval (α i) * e i) /
          rsBarycentricDenominator α i) =
        ∑ i : ι, ∑ j : Fin c,
          α i ^ t *
              ((Polynomial.degreeLTEquiv K c A) j * α i ^ j.1 * e i) /
            rsBarycentricDenominator α i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.eval_eq_sum_degreeLTEquiv A.2,
        Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    _ = ∑ j : Fin c, ∑ i : ι,
          α i ^ t *
              ((Polynomial.degreeLTEquiv K c A) j * α i ^ j.1 * e i) /
            rsBarycentricDenominator α i := Finset.sum_comm
    _ = ∑ j : Fin c,
        (Polynomial.degreeLTEquiv K c A) j *
          (∑ i : ι,
            α i ^ (t + j.1) * e i /
              rsBarycentricDenominator α i) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      ring

/-- The syndrome moment commutes with a coefficient automorphism which fixes
the evaluation domain. -/
theorem map_rsSyndromeMoment
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i)
    (e : ι → K) (t : ℕ) :
    sigma (rsSyndromeMoment α e t) =
      rsSyndromeMoment α (fun i => sigma (e i)) t := by
  classical
  simp only [rsSyndromeMoment, map_sum, map_div₀, map_mul, map_pow,
    hfixed, map_rsBarycentricDenominator α sigma hfixed]

theorem polynomial_map_eval_of_fixed_locator
    (sigma : K ≃+* K) (P : K[X]) (x : K) (hx : sigma x = x) :
    (P.map sigma.toRingHom).eval x = sigma (P.eval x) := by
  have h := Polynomial.eval_map_apply (p := P) sigma.toRingHom x
  have hx' : sigma.toRingHom x = x := hx
  calc
    (P.map sigma.toRingHom).eval x =
        sigma.toRingHom (P.eval x) := by simpa only [hx'] using h
    _ = sigma (P.eval x) := rfl

theorem rsSyndromeMoment_add
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e₀ e₁ : ι → K) (t : ℕ) :
    rsSyndromeMoment α (fun i => e₀ i + e₁ i) t =
      rsSyndromeMoment α e₀ t + rsSyndromeMoment α e₁ t := by
  simpa using rsSyndromeMoment_affine α e₀ e₁ 1 t

theorem rsSyndromeMoment_sub
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e₀ e₁ : ι → K) (t : ℕ) :
    rsSyndromeMoment α (fun i => e₀ i - e₁ i) t =
      rsSyndromeMoment α e₀ t - rsSyndromeMoment α e₁ t := by
  classical
  simp only [rsSyndromeMoment]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem natDegree_lt_of_degreeLT_element
    (d : ℕ) (hd : 0 < d) (P : Polynomial.degreeLT K d) :
    P.1.natDegree < d := by
  by_cases hP : P.1 = 0
  · simpa only [hP, Polynomial.natDegree_zero] using hd
  · exact (Polynomial.natDegree_lt_iff_degree_lt hP).2
      (Polynomial.mem_degreeLT.mp P.2)

theorem polynomialPairDet_eval
    {c h : ℕ} (u v : PolynomialPairSpace K c h) (x : K) :
    (polynomialPairDet u v).eval x =
      u.1.1.eval x * v.2.1.eval x -
        u.2.1.eval x * v.1.1.eval x := by
  simp only [polynomialPairDet, Polynomial.eval_sub, Polynomial.eval_mul]

theorem polynomialPairDet_eval_eq_zero_of_error_ne_zero
    {c h : ℕ} (u v : PolynomialPairSpace K c h) (x e ep : K)
    (he : e ≠ 0)
    (hu : u.1.1.eval x * e + u.2.1.eval x * ep = 0)
    (hv : v.1.1.eval x * e + v.2.1.eval x * ep = 0) :
    (polynomialPairDet u v).eval x = 0 := by
  rw [polynomialPairDet_eval]
  simpa only [mul_comm] using
    (pairDet_eq_zero_of_error_ne_zero
      (u.1.1.eval x) (u.2.1.eval x)
      (v.1.1.eval x) (v.2.1.eval x) e ep he hu hv)

/-- Coefficient coordinates of a production-pencil kernel vector, packaged
as its ordinary and Frobenius multiplier polynomials. -/
noncomputable def score6400LocatorRelationPair
    (q : Score6400LocatorMinorIndex → IRSProfile.Field) :
    PolynomialPairSpace IRSProfile.Field locatorOrdinaryRows6400
      locatorFrobeniusRows6400 :=
  (mixedStackDomainEquiv
    locatorOrdinaryRows6400 locatorFrobeniusRows6400).symm q

@[simp]
theorem score6400LocatorRelationPair_inl_coeff
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (i : Fin locatorOrdinaryRows6400) :
    (Polynomial.degreeLTEquiv IRSProfile.Field locatorOrdinaryRows6400
      (score6400LocatorRelationPair q).1) i = q (Sum.inl i) := by
  have h := congrFun
    ((mixedStackDomainEquiv
      locatorOrdinaryRows6400 locatorFrobeniusRows6400).apply_symm_apply q)
      (Sum.inl i)
  simpa only [score6400LocatorRelationPair, mixedStackDomainEquiv,
    LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl] using h

@[simp]
theorem score6400LocatorRelationPair_inr_coeff
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (i : Fin locatorFrobeniusRows6400) :
    (Polynomial.degreeLTEquiv IRSProfile.Field locatorFrobeniusRows6400
      (score6400LocatorRelationPair q).2) i = q (Sum.inr i) := by
  have h := congrFun
    ((mixedStackDomainEquiv
      locatorOrdinaryRows6400 locatorFrobeniusRows6400).apply_symm_apply q)
      (Sum.inr i)
  simpa only [score6400LocatorRelationPair, mixedStackDomainEquiv,
    LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr] using h

/-- A vector in the concrete locator-pencil kernel gives all `76781`
syndrome moments of the corresponding received-word relation. -/
theorem score6400_locatorKernel_received_relation_moment
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : q ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (t : ℕ) (ht : t < locatorColumns6400) :
    rsSyndromeMoment IRSProfile.domain
        (fun i =>
          (score6400LocatorRelationPair q).1.1.eval
                (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
            (score6400LocatorRelationPair q).2.1.eval
                (IRSProfile.domain i) *
              koalaSexticFrobenius (f₀ i + z * f₁ i)) t = 0 := by
  classical
  rw [LinearMap.mem_ker] at hq
  let coefficient : Score6400LocatorMinorIndex :=
    score6400LocatorCoefficientEquiv.symm ⟨t, ht⟩
  have hrow := congrFun hq coefficient
  have hordinary := rsSyndromeMoment_eval_mul
    IRSProfile.domain (fun i => f₀ i + z * f₁ i)
    locatorOrdinaryRows6400 t (score6400LocatorRelationPair q).1
  have hfrobenius := rsSyndromeMoment_eval_mul
    IRSProfile.domain
    (fun i => koalaSexticFrobenius (f₀ i + z * f₁ i))
    locatorFrobeniusRows6400 t (score6400LocatorRelationPair q).2
  rw [rsSyndromeMoment_add]
  rw [hordinary, hfrobenius]
  simp only [score6400LocatorRelationPair_inl_coeff,
    score6400LocatorRelationPair_inr_coeff]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Pi.zero_apply, Fintype.sum_sum_type] at hrow
  have hcoefficient : score6400LocatorCoefficientEquiv coefficient =
      (⟨t, ht⟩ : Fin locatorColumns6400) := by
    exact score6400LocatorCoefficientEquiv.apply_symm_apply ⟨t, ht⟩
  simp_rw [score6400LocatorStack_specialize_ordinary,
    score6400LocatorStack_specialize_frobenius] at hrow
  rw [hcoefficient] at hrow
  -- Each Frobenius stack entry is the moment of the conjugated word because
  -- the NTT domain and its barycentric denominators lie in the fixed field.
  simp_rw [map_rsSyndromeMoment IRSProfile.domain koalaSexticFrobenius
    koalaSexticFrobenius_fixed_domain] at hrow
  simpa only [add_comm, mul_comm] using hrow

/-- The syndrome relation produced by a concrete kernel vector is a genuine
pointwise semilinear relation for the error relative to any close
Reed--Solomon polynomial. -/
theorem score6400_locatorKernel_error_relation_of_agreement
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : q ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAcard : 185364 ≤ A.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) :
    ∀ i,
      (score6400LocatorRelationPair q).1.1.eval
            (IRSProfile.domain i) *
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        (score6400LocatorRelationPair q).2.1.eval
            (IRSProfile.domain i) *
          koalaSexticFrobenius
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) = 0 := by
  classical
  let u := score6400LocatorRelationPair q
  let received : IRSProfile.Index → IRSProfile.Field := fun i =>
    u.1.1.eval (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
      u.2.1.eval (IRSProfile.domain i) *
        koalaSexticFrobenius (f₀ i + z * f₁ i)
  let codeword : IRSProfile.Index → IRSProfile.Field := fun i =>
    u.1.1.eval (IRSProfile.domain i) * P.eval (IRSProfile.domain i) +
      u.2.1.eval (IRSProfile.domain i) *
        koalaSexticFrobenius (P.eval (IRSProfile.domain i))
  let relationError : IRSProfile.Index → IRSProfile.Field := fun i =>
    u.1.1.eval (IRSProfile.domain i) *
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
      u.2.1.eval (IRSProfile.domain i) *
        koalaSexticFrobenius
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i))
  have hrelationError : relationError = fun i => received i - codeword i := by
    funext i
    simp only [relationError, received, codeword, map_sub]
    ring
  have hu₀degree : u.1.1.natDegree < locatorOrdinaryRows6400 :=
    natDegree_lt_of_degreeLT_element locatorOrdinaryRows6400 (by norm_num)
      u.1
  have hu₁degree : u.2.1.natDegree < locatorFrobeniusRows6400 :=
    natDegree_lt_of_degreeLT_element locatorFrobeniusRows6400 (by norm_num)
      u.2
  have hu₀cap : u.1.1.natDegree ≤ 54291 := by
    norm_num [locatorOrdinaryRows6400] at hu₀degree ⊢
    omega
  have hu₁cap : u.2.1.natDegree ≤ 22488 := by
    norm_num [locatorFrobeniusRows6400] at hu₁degree ⊢
    omega
  let codePolynomial : IRSProfile.Field[X] :=
    u.1.1 * P +
      u.2.1 * P.map koalaSexticFrobenius.toRingHom
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
      apply max_le
      · exact hleftCap
      · exact hrightCap.trans (by norm_num)
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
    simpa only [received, u] using
      score6400_locatorKernel_received_relation_moment f₀ f₁ z q hq t ht
  have herrorMoment : ∀ t < locatorColumns6400,
      rsSyndromeMoment IRSProfile.domain relationError t = 0 := by
    intro t ht
    rw [hrelationError, rsSyndromeMoment_sub,
      hreceivedMoment t ht, hcodeMoment t ht, sub_zero]
  have hzeroA : ∀ i ∈ A, relationError i = 0 := by
    intro i hi
    simp only [relationError, hagree i hi, sub_self, map_zero, mul_zero,
      add_zero]
  have hall := rsSyndromeMoment_eq_zero_of_prefix_and_many_zeros
    IRSProfile.domain relationError locatorColumns6400
    (by norm_num [locatorColumns6400, IRSProfile.Index]) herrorMoment A
    (by
      norm_num [locatorColumns6400, IRSProfile.Index]
      omega)
    hzeroA
  simpa only [relationError, u] using hall

/-- Every score-64 bad witness therefore turns every specialized production
kernel vector into a global semilinear relation for one actual error word. -/
theorem exists_score6400_error_relation_of_locatorKernel_and_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : q ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin) :
    ∃ P : IRSProfile.Field[X],
      P.natDegree ≤ 131071 ∧
      185364 ≤ (Finset.univ.filter fun i =>
        P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i).card ∧
      ∀ i,
        (score6400LocatorRelationPair q).1.1.eval
              (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
          (score6400LocatorRelationPair q).2.1.eval
              (IRSProfile.domain i) *
            koalaSexticFrobenius
              ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) = 0 := by
  classical
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      f₀ f₁ 185364 z := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨A, P, hA, hPdegree, hPagree, _⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 f₀ f₁ z hbadRS
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · subst P
      norm_num
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  have hAfilter : A ⊆ Finset.univ.filter fun i =>
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPagree i hi⟩
  refine ⟨P, hPnat, hA.trans (Finset.card_le_card hAfilter), ?_⟩
  exact score6400_locatorKernel_error_relation_of_agreement
    f₀ f₁ z q hq A P hA hPnat hPagree

/-- Two specialized production-kernel vectors have alternating determinant
zero at every genuine error coordinate of the same decoding witness. -/
theorem score6400_two_locatorKernels_pairDet_root_of_agreement
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (q₀ q₁ : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq₀ : q₀ ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (hq₁ : q₁ ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAcard : 185364 ≤ A.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i)
    (i : IRSProfile.Index)
    (hiError : (f₀ i + z * f₁ i) -
      P.eval (IRSProfile.domain i) ≠ 0) :
    (polynomialPairDet
      (score6400LocatorRelationPair q₀)
      (score6400LocatorRelationPair q₁)).eval
        (IRSProfile.domain i) = 0 := by
  have hrel₀ := score6400_locatorKernel_error_relation_of_agreement
    f₀ f₁ z q₀ hq₀ A P hAcard hPdegree hagree i
  have hrel₁ := score6400_locatorKernel_error_relation_of_agreement
    f₀ f₁ z q₁ hq₁ A P hAcard hPdegree hagree i
  exact polynomialPairDet_eval_eq_zero_of_error_ne_zero
    (score6400LocatorRelationPair q₀)
    (score6400LocatorRelationPair q₁) (IRSProfile.domain i)
    ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i))
    (koalaSexticFrobenius
      ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)))
    hiError hrel₀ hrel₁

/-- Score-64 wrapper of the two-relation determinant-root statement.  The
same Reed--Solomon witness is used for both relations. -/
theorem exists_score6400_pairDet_roots_of_two_locatorKernels_and_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (q₀ q₁ : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq₀ : q₀ ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (hq₁ : q₁ ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin) :
    ∃ P : IRSProfile.Field[X],
      P.natDegree ≤ 131071 ∧
      185364 ≤ (Finset.univ.filter fun i =>
        P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i).card ∧
      ∀ i, (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0 →
        (polynomialPairDet
          (score6400LocatorRelationPair q₀)
          (score6400LocatorRelationPair q₁)).eval
            (IRSProfile.domain i) = 0 := by
  classical
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      f₀ f₁ 185364 z := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨A, P, hA, hPdegree, hPagree, _⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 f₀ f₁ z hbadRS
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · subst P
      norm_num
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  have hAfilter : A ⊆ Finset.univ.filter fun i =>
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPagree i hi⟩
  refine ⟨P, hPnat, hA.trans (Finset.card_le_card hAfilter), ?_⟩
  intro i hi
  exact score6400_two_locatorKernels_pairDet_root_of_agreement
    f₀ f₁ z q₀ q₁ hq₀ hq₁ A P hA hPnat hPagree i hi

/-- After removing slopes which are already bad at the accepted score-63.99
agreement threshold, the decoding witness used by the two-relation argument
has at least `76771` genuine errors. -/
theorem exists_score6400_large_error_support_pairDet_roots
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z)
    (q₀ q₁ : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq₀ : q₀ ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (hq₁ : q₁ ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin) :
    ∃ P : IRSProfile.Field[X], ∃ E : Finset IRSProfile.Index,
      P.natDegree ≤ 131071 ∧
      E = Finset.univ.filter (fun i =>
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0) ∧
      76771 ≤ E.card ∧
      ∀ i ∈ E,
        (polynomialPairDet
          (score6400LocatorRelationPair q₀)
          (score6400LocatorRelationPair q₁)).eval
            (IRSProfile.domain i) = 0 := by
  classical
  rcases hbad with ⟨A, hA, hline, hpair⟩
  rcases hline with ⟨c, hc, hcAgree⟩
  have hcRS : c ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension := by
    simpa only [IRSProfile.baseCode] using hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcRS
  obtain ⟨P, hPdegree, hPc⟩ := hcRS
  subst c
  have hPagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    have h := hcAgree i hi
    change P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i at h
    exact h
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · subst P
      norm_num
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  let E : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i
  have hAG : A ⊆ G := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPagree i hi⟩
  have hpartition : E.card + G.card = 262144 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun i : IRSProfile.Index =>
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0)
      (s := Finset.univ)
    have hfirst : (Finset.univ.filter fun i : IRSProfile.Index =>
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0) = E := rfl
    have hsecond : (Finset.univ.filter fun i : IRSProfile.Index =>
        ¬((f₀ i + z * f₁ i) -
          P.eval (IRSProfile.domain i) ≠ 0)) = G := by
      ext i
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and,
        not_ne_iff, sub_eq_zero]
      exact eq_comm
    rw [hfirst, hsecond] at hsplit
    calc
      E.card + G.card = Finset.univ.card := hsplit
      _ = 262144 := by norm_num [IRSProfile.Index]
  have hEcard : 76771 ≤ E.card := by
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
        (fun i hi => h₀ i (hAG hi)),
        (fun i hi => h₁ i (hAG hi))⟩
  refine ⟨P, E, hPnat, rfl, hEcard, ?_⟩
  intro i hi
  have hiError := (Finset.mem_filter.mp hi).2
  exact score6400_two_locatorKernels_pairDet_root_of_agreement
    f₀ f₁ z q₀ q₁ hq₀ hq₁ A P hA hPnat hPagree i hiError

/-- The decoding witness and its large genuine-error support depend only on
the bad slope, not on which locator-kernel vectors will later be paired. -/
theorem exists_score6400_large_error_witness
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∃ A : Finset IRSProfile.Index, ∃ P : IRSProfile.Field[X],
      ∃ E : Finset IRSProfile.Index,
        185364 ≤ A.card ∧
        P.natDegree ≤ 131071 ∧
        (∀ i ∈ A,
          P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) ∧
        ¬BCHKSExactSparsification6400.ExplainedPair
          IRSProfile.baseCode f₀ f₁ A ∧
        E = Finset.univ.filter (fun i =>
          (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0) ∧
        76771 ≤ E.card ∧ E.card ≤ 76780 := by
  classical
  rcases hbad with ⟨A, hA, hline, hpair⟩
  rcases hline with ⟨c, hc, hcAgree⟩
  have hcRS : c ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension := by
    simpa only [IRSProfile.baseCode] using hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcRS
  obtain ⟨P, hPdegree, hPc⟩ := hcRS
  subst c
  have hPagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    have h := hcAgree i hi
    change P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i at h
    exact h
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · subst P
      norm_num
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  let E : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i
  have hAG : A ⊆ G := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPagree i hi⟩
  have hpartition : E.card + G.card = 262144 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun i : IRSProfile.Index =>
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0)
      (s := Finset.univ)
    have hfirst : (Finset.univ.filter fun i : IRSProfile.Index =>
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0) = E := rfl
    have hsecond : (Finset.univ.filter fun i : IRSProfile.Index =>
        ¬((f₀ i + z * f₁ i) -
          P.eval (IRSProfile.domain i) ≠ 0)) = G := by
      ext i
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and,
        not_ne_iff, sub_eq_zero]
      exact eq_comm
    rw [hfirst, hsecond] at hsplit
    calc
      E.card + G.card = Finset.univ.card := hsplit
      _ = 262144 := by norm_num [IRSProfile.Index]
  have hEcard : 76771 ≤ E.card := by
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
        (fun i hi => h₀ i (hAG hi)),
        (fun i hi => h₁ i (hAG hi))⟩
  have hEupper : E.card ≤ 76780 := by
    have hGcard : 185364 ≤ G.card :=
      hA.trans (Finset.card_le_card hAG)
    omega
  exact ⟨A, P, E, hA, hPnat, hPagree, hpair, rfl,
    hEcard, hEupper⟩

/-- One bad-slope witness supplies a common large error support on which all
pair determinants from an arbitrary family of specialized locator-kernel
vectors vanish. -/
theorem exists_score6400_large_error_support_pairDet_roots_family
    {J : Type}
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z)
    (q : J → Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : ∀ j, q j ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin) :
    ∃ A : Finset IRSProfile.Index, ∃ P : IRSProfile.Field[X],
      ∃ E : Finset IRSProfile.Index,
      185364 ≤ A.card ∧
      P.natDegree ≤ 131071 ∧
      (∀ i ∈ A,
        P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) ∧
      ¬BCHKSExactSparsification6400.ExplainedPair
        IRSProfile.baseCode f₀ f₁ A ∧
      E = Finset.univ.filter (fun i =>
        (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0) ∧
      76771 ≤ E.card ∧ E.card ≤ 76780 ∧
      ∀ j₀ j₁ i, i ∈ E →
        (polynomialPairDet
          (score6400LocatorRelationPair (q j₀))
          (score6400LocatorRelationPair (q j₁))).eval
            (IRSProfile.domain i) = 0 := by
  obtain ⟨A, P, E, hA, hPdegree, hagree, hpair, hE,
      hEcard, hEupper⟩ :=
    exists_score6400_large_error_witness f₀ f₁ z hbad hnotOld
  refine ⟨A, P, E, hA, hPdegree, hagree, hpair, hE,
    hEcard, hEupper, ?_⟩
  intro j₀ j₁ i hi
  have hiError : (f₀ i + z * f₁ i) -
      P.eval (IRSProfile.domain i) ≠ 0 := by
    rw [hE] at hi
    exact (Finset.mem_filter.mp hi).2
  exact score6400_two_locatorKernels_pairDet_root_of_agreement
    f₀ f₁ z (q j₀) (q j₁) (hq j₀) (hq j₁)
      A P hA hPdegree hagree i hiError

end ProximityPrize.SubmissionLower

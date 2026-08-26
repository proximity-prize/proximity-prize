import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401

/-!
# Rectangular support audit for the score-64.01 key-equation fork

The standard syndrome factorization has three independent sizes:

* the number of check rows in each lane;
* the actual number `e` of nonzero error positions;
* the proposed locator degree, hence the number `cols` of unknown locator
  coefficients.

The right Vandermonde is `e x cols`.  It is square only when the proposed
locator degree is the actual error weight.  This distinction matters for a
closed Hamming ball: the benchmark assumptions give only `e <= 76790`.
If `e < 76790`, the fixed `76790`-column two-lane matrix is rank deficient
for dimension reasons, independently of the error values and independently
of the Frobenius relation between the lanes.  Such a defect can be witnessed
by a locator polynomial vanishing on the entire error support, and therefore
does not by itself yield a nonzero primitive two-Frobenius row.

This file proves the exact rectangular factorization and its unavoidable
rank bound.  It does not modify the square, exact-weight factorization in
`BCHKSFrobeniusKeyEquationFork6401`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusRectangularHankelAudit6401

open Polynomial
open scoped BigOperators
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSSphericalL3Radius76855Audit6401

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

/-- The rectangular right Vandermonde: actual support positions index rows,
while proposed locator coefficients index columns. -/
def rectangularSyndromeRightVandermonde
    {F : Type*} [Field F] {e : Nat} (cols : Nat)
    (alpha : Fin e → F) : Matrix (Fin e) (Fin cols) F :=
  fun i j => alpha i ^ j.1

/-- Two Hankel syndrome lanes with a common actual support of size `e` and
an arbitrary proposed locator width `cols`. -/
def twoLaneSupportSyndromeMatrix
    {F : Type*} [Field F] {e : Nat}
    (rows₀ rows₁ cols : Nat) (alpha d₀ d₁ : Fin e → F) :
    Matrix (Fin rows₀ ⊕ Fin rows₁) (Fin cols) F
  | Sum.inl i, j =>
      BCHKSFrobeniusKeyEquationFork6401.supportSyndrome alpha d₀ (i.1 + j.1)
  | Sum.inr i, j =>
      BCHKSFrobeniusKeyEquationFork6401.supportSyndrome alpha d₁ (i.1 + j.1)

/-- The left factor combines the two shortened Vandermonde check matrices
and their lane-specific weighted error values. -/
def twoLaneSupportLeftFactor
    {F : Type*} [Field F] {e : Nat}
    (rows₀ rows₁ : Nat) (alpha d₀ d₁ : Fin e → F) :
    Matrix (Fin rows₀ ⊕ Fin rows₁) (Fin e) F
  | Sum.inl i, j => d₀ j * alpha j ^ i.1
  | Sum.inr i, j => d₁ j * alpha j ^ i.1

/-- Exact rectangular two-lane Hankel--Vandermonde factorization.

`M = L * V`, where `L` has one column per actual error and `V` evaluates
the proposed locator coefficients on those actual error positions. -/
theorem twoLaneSupportSyndromeMatrix_factorization
    {F : Type*} [Field F] {e : Nat}
    (rows₀ rows₁ cols : Nat) (alpha d₀ d₁ : Fin e → F) :
    twoLaneSupportSyndromeMatrix rows₀ rows₁ cols alpha d₀ d₁ =
      twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁ *
        rectangularSyndromeRightVandermonde cols alpha := by
  classical
  ext i j
  rcases i with i | i
  · simp only [twoLaneSupportSyndromeMatrix, twoLaneSupportLeftFactor,
      rectangularSyndromeRightVandermonde, Matrix.mul_apply,
      BCHKSFrobeniusKeyEquationFork6401.supportSyndrome]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [pow_add]
    ring
  · simp only [twoLaneSupportSyndromeMatrix, twoLaneSupportLeftFactor,
      rectangularSyndromeRightVandermonde, Matrix.mul_apply,
      BCHKSFrobeniusKeyEquationFork6401.supportSyndrome]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [pow_add]
    ring

/-- The rank of the stacked system is at most the actual support size, no
matter how many locator columns or syndrome rows are requested. -/
theorem twoLaneSupportSyndromeMatrix_rank_le_support
    {F : Type*} [Field F] {e : Nat}
    (rows₀ rows₁ cols : Nat) (alpha d₀ d₁ : Fin e → F) :
    (twoLaneSupportSyndromeMatrix rows₀ rows₁ cols alpha d₀ d₁).rank ≤ e := by
  rw [twoLaneSupportSyndromeMatrix_factorization]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using
    (Matrix.rank_le_card_width
      (twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁))

/-- With distinct support locations and at least as many proposed locator
columns as actual errors, the right rectangular Vandermonde has full row
rank. -/
theorem rectangularSyndromeRightVandermonde_rank_eq_support
    {F : Type*} [Field F] {e cols : Nat}
    (alpha : Fin e → F) (halpha : Function.Injective alpha)
    (he : e ≤ cols) :
    (rectangularSyndromeRightVandermonde cols alpha).rank = e := by
  rw [show rectangularSyndromeRightVandermonde cols alpha =
      Vandermonde.nonsquare cols alpha by rfl]
  exact Vandermonde.rank_nonsquare_eq_deg_of_ι_le halpha he

/-- Right multiplication by the full-row-rank rectangular Vandermonde does
not change rank.  This is the exact linear-algebra statement needed to
quotient out locator polynomials which vanish on the entire support. -/
theorem twoLaneSupportSyndromeMatrix_rank_eq_leftFactor
    {F : Type*} [Field F] {e cols : Nat}
    (rows₀ rows₁ : Nat) (alpha d₀ d₁ : Fin e → F)
    (halpha : Function.Injective alpha) (he : e ≤ cols) :
    (twoLaneSupportSyndromeMatrix rows₀ rows₁ cols alpha d₀ d₁).rank =
      (twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁).rank := by
  classical
  rw [twoLaneSupportSyndromeMatrix_factorization]
  apply le_antisymm
  · exact Matrix.rank_mul_le_left _ _
  · let c : Fin e → Fin cols := Fin.castLE he
    let L := twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁
    let V := rectangularSyndromeRightVandermonde cols alpha
    have hVsub : V.submatrix id c = Matrix.vandermonde alpha := by
      ext i j
      rfl
    have hsub : (L * V).submatrix id c = L * Matrix.vandermonde alpha := by
      rw [Matrix.submatrix_mul L V id (Equiv.refl (Fin e)) c
        (Equiv.refl (Fin e)).bijective]
      simp only [Equiv.coe_refl, Matrix.submatrix_id_id, hVsub]
    have hdet : IsUnit (Matrix.vandermonde alpha).det :=
      isUnit_iff_ne_zero.mpr
        (Matrix.det_vandermonde_ne_zero_iff.mpr halpha)
    have hrankSub : ((L * V).submatrix id c).rank = L.rank := by
      rw [hsub]
      exact Matrix.rank_mul_eq_left_of_isUnit_det
        (Matrix.vandermonde alpha) L hdet
    rw [← hrankSub]
    exact Matrix.rank_submatrix_le (L * V) id c

/-- A matrix whose rank is below its column count has a nonzero right-kernel
vector.  Kept local to this independent audit helper. -/
theorem exists_nonzero_mulVec_eq_zero_of_rank_lt_width
    {F Row Col : Type*} [Field F]
    [Fintype Row] [Fintype Col]
    (M : Matrix Row Col F)
    (hrank : M.rank < Fintype.card Col) :
    ∃ v : Col → F, v ≠ 0 ∧ M.mulVec v = 0 := by
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hbot
    have hnull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have heq : M.rank = Fintype.card Col := by
      rw [hbot] at hnull
      simpa [Matrix.rank] using hnull
    exact (Nat.ne_of_lt hrank) heq
  obtain ⟨v, hvker, hvne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hvne, ?_⟩
  simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hvker

/-- After removing the rectangular Vandermonde's support-vanishing kernel,
a genuine rank defect is exactly a nonzero kernel vector of the left support
matrix. -/
theorem exists_nonzero_supportKernel_of_rank_lt_support
    {F : Type*} [Field F] {e cols : Nat}
    (rows₀ rows₁ : Nat) (alpha d₀ d₁ : Fin e → F)
    (halpha : Function.Injective alpha) (he : e ≤ cols)
    (hrank :
      (twoLaneSupportSyndromeMatrix rows₀ rows₁ cols alpha d₀ d₁).rank < e) :
    ∃ v : Fin e → F, v ≠ 0 ∧
      (twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁).mulVec v = 0 := by
  have hleft :
      (twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁).rank <
        Fintype.card (Fin e) := by
    rw [Fintype.card_fin, ←
      twoLaneSupportSyndromeMatrix_rank_eq_leftFactor
        rows₀ rows₁ alpha d₀ d₁ halpha he]
    exact hrank
  exact exists_nonzero_mulVec_eq_zero_of_rank_lt_width _ hleft

/-- Pointwise generic-rank stratification.  If a specialization has rank
`ρ` and an owner has actual support size `e`, then `ρ ≤ e`.  Equality is
the exact-weight/locator case.  Strict inequality gives a nonzero kernel of
the left support factor, rather than merely a locator polynomial in the
automatic kernel of the rectangular right Vandermonde. -/
theorem support_eq_rank_or_nonzero_supportKernel
    {F : Type*} [Field F] {ρ e cols : Nat}
    (rows₀ rows₁ : Nat) (alpha d₀ d₁ : Fin e → F)
    (halpha : Function.Injective alpha) (he : e ≤ cols)
    (hrank :
      (twoLaneSupportSyndromeMatrix rows₀ rows₁ cols alpha d₀ d₁).rank = ρ) :
    ρ ≤ e ∧
      (e = ρ ∨
        ∃ v : Fin e → F, v ≠ 0 ∧
          (twoLaneSupportLeftFactor rows₀ rows₁ alpha d₀ d₁).mulVec v = 0) := by
  have hρe : ρ ≤ e := by
    rw [← hrank]
    exact twoLaneSupportSyndromeMatrix_rank_le_support
      rows₀ rows₁ cols alpha d₀ d₁
  refine ⟨hρe, ?_⟩
  rcases hρe.eq_or_lt with hEq | hLt
  · exact Or.inl hEq.symm
  · apply Or.inr
    apply exists_nonzero_supportKernel_of_rank_lt_support
      rows₀ rows₁ alpha d₀ d₁ halpha he
    simpa [hrank] using hLt

/-! ## Exact shortened dual-Vandermonde polynomialization -/

/-- The derivative/coweight of the error-support locator at one support
point.  Its inverse is `Lagrange.nodalWeight` on the support. -/
noncomputable def supportCoweight
    {F : Type*} [Field F] {e : Nat}
    (alpha : Fin e → F) (i : Fin e) : F :=
  ∏ j ∈ (Finset.univ : Finset (Fin e)).erase i, (alpha i - alpha j)

theorem supportCoweight_ne_zero
    {F : Type*} [Field F] {e : Nat}
    (alpha : Fin e → F) (halpha : Function.Injective alpha) (i : Fin e) :
    supportCoweight alpha i ≠ 0 := by
  unfold supportCoweight
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr (halpha.ne hji.symm)

/-- Interpolate the support vector after multiplying by the support-locator
coweight.  This is the polynomial representative of a word annihilated by
the raw Vandermonde parity checks. -/
noncomputable def supportDualPolynomial
    {F : Type*} [Field F] {e : Nat}
    (alpha x : Fin e → F) : Polynomial F :=
  Lagrange.interpolate Finset.univ alpha
    (fun i => x i * supportCoweight alpha i)

theorem supportDualPolynomial_eval
    {F : Type*} [Field F] {e : Nat}
    (alpha x : Fin e → F) (halpha : Function.Injective alpha) (i : Fin e) :
    (supportDualPolynomial alpha x).eval (alpha i) =
      x i * supportCoweight alpha i := by
  unfold supportDualPolynomial
  exact Lagrange.eval_interpolate_at_node _ halpha.injOn
    (Finset.mem_univ i)

/-- Exact converse to the shortened Vandermonde parity checks.  If the
first `rows` moments of `x` vanish and `rows < e`, then after the common
nonzero coweight the vector is the evaluation of a polynomial of degree
strictly below `e - rows`.

This is deterministic dual Reed--Solomon algebra, not a generic-success
claim. -/
theorem supportDualPolynomial_natDegree_lt
    {F : Type*} [Field F] {e rows : Nat}
    (alpha x : Fin e → F) (halpha : Function.Injective alpha)
    (hrows : rows < e)
    (hmoments : ∀ r : Fin rows, ∑ i, x i * alpha i ^ r.1 = 0) :
    (supportDualPolynomial alpha x).natDegree < e - rows := by
  classical
  let W := supportDualPolynomial alpha x
  have hWdegree : W.degree < (e : WithBot Nat) := by
    simpa [W, supportDualPolynomial] using
      (Lagrange.degree_interpolate_lt
        (s := (Finset.univ : Finset (Fin e)))
        (r := fun i => x i * supportCoweight alpha i)
        halpha.injOn)
  by_cases hWzero : W = 0
  · simp [W, hWzero, Nat.sub_pos_of_lt hrows]
  have hWnat : W.natDegree < e :=
    (Polynomial.natDegree_lt_iff_degree_lt hWzero).2 hWdegree
  by_contra hnot
  have hlarge : e - rows ≤ W.natDegree := Nat.le_of_not_gt hnot
  let j : Nat := e - 1 - W.natDegree
  have hjrows : j < rows := by
    dsimp [j]
    omega
  have hsum : ∑ i, x i * alpha i ^ j = 0 :=
    hmoments ⟨j, hjrows⟩
  let Q : Polynomial F := W * Polynomial.X ^ j
  have hXpow : (Polynomial.X : Polynomial F) ^ j ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hQzero : Q ≠ 0 := by
    exact mul_ne_zero hWzero hXpow
  have hjadd : W.natDegree + j = e - 1 := by
    dsimp [j]
    omega
  have hQnat : Q.natDegree < e := by
    rw [show Q.natDegree = W.natDegree + j by
      calc
        Q.natDegree = W.natDegree +
            ((Polynomial.X : Polynomial F) ^ j).natDegree := by
          exact Polynomial.natDegree_mul hWzero hXpow
        _ = W.natDegree + j := by simp]
    omega
  have hQdegree : Q.degree < (e : WithBot Nat) :=
    (Polynomial.natDegree_lt_iff_degree_lt hQzero).1 hQnat
  have hc := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin e))) (v := alpha)
    halpha.injOn (by simpa using hQdegree)
  have hc0 : Q.coeff (e - 1) = 0 := by
    rw [show Q.coeff (e - 1) =
        ∑ i : Fin e, Q.eval (alpha i) /
          ∏ k ∈ (Finset.univ : Finset (Fin e)).erase i,
            (alpha i - alpha k) by simpa using hc]
    calc
      (∑ i : Fin e, Q.eval (alpha i) /
          ∏ k ∈ (Finset.univ : Finset (Fin e)).erase i,
            (alpha i - alpha k)) =
          ∑ i : Fin e, x i * alpha i ^ j := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hco := supportCoweight_ne_zero alpha halpha i
        have hWeval : W.eval (alpha i) =
            x i * supportCoweight alpha i := by
          simpa [W] using supportDualPolynomial_eval alpha x halpha i
        rw [show Q.eval (alpha i) =
            (x i * supportCoweight alpha i) * alpha i ^ j by
          simp only [Q, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, hWeval]]
        unfold supportCoweight at hco ⊢
        field_simp
      _ = 0 := hsum
  have hcoeffne : Q.coeff (e - 1) ≠ 0 := by
    dsimp [Q]
    rw [← hjadd, Polynomial.coeff_mul_X_pow,
      Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hWzero
  exact hcoeffne hc0

/-- A genuine left-factor kernel produces the nonzero denominator-free
two-lane relation.  The common factor is the product of the full-domain
parity weight and the support-locator coweight; it cancels without division.
-/
theorem exists_failureRelation_of_nonzero_supportKernel
    {F : Type*} [Field F] {e rows : Nat}
    (sigma : F →+* F) (alpha E weight v : Fin e → F)
    (halpha : Function.Injective alpha) (hrows : rows < e)
    (hweight : ∀ i, weight i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hv : v ≠ 0)
    (hker :
      (twoLaneSupportLeftFactor rows rows alpha
        (fun i => weight i * E i)
        (fun i => weight i * sigma (E i))).mulVec v = 0) :
    ∃ W₀ W₁ : Polynomial F,
      W₀ ≠ 0 ∧
      W₀.natDegree < e - rows ∧
      W₁.natDegree < e - rows ∧
      TwoLaneFailureRelation sigma alpha E W₀ W₁ := by
  classical
  let x₀ : Fin e → F := fun i => weight i * E i * v i
  let x₁ : Fin e → F := fun i => weight i * sigma (E i) * v i
  let W₀ := supportDualPolynomial alpha x₀
  let W₁ := supportDualPolynomial alpha x₁
  have hmom₀ : ∀ r : Fin rows, ∑ i, x₀ i * alpha i ^ r.1 = 0 := by
    intro r
    have hr := congrFun hker (Sum.inl r)
    simpa [twoLaneSupportLeftFactor, Matrix.mulVec, dotProduct,
      x₀, mul_assoc, mul_left_comm, mul_comm] using hr
  have hmom₁ : ∀ r : Fin rows, ∑ i, x₁ i * alpha i ^ r.1 = 0 := by
    intro r
    have hr := congrFun hker (Sum.inr r)
    simpa [twoLaneSupportLeftFactor, Matrix.mulVec, dotProduct,
      x₁, mul_assoc, mul_left_comm, mul_comm] using hr
  have hW₀deg : W₀.natDegree < e - rows := by
    exact supportDualPolynomial_natDegree_lt
      alpha x₀ halpha hrows hmom₀
  have hW₁deg : W₁.natDegree < e - rows := by
    exact supportDualPolynomial_natDegree_lt
      alpha x₁ halpha hrows hmom₁
  have hW₀ne : W₀ ≠ 0 := by
    intro hzero
    apply hv
    funext i
    have hi := supportDualPolynomial_eval alpha x₀ halpha i
    have hizero : x₀ i * supportCoweight alpha i = 0 := by
      rw [← hi]
      change W₀.eval (alpha i) = 0
      rw [hzero, Polynomial.eval_zero]
    by_contra hvi
    exact (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hweight i) (hE i)) hvi)
        (supportCoweight_ne_zero alpha halpha i)) hizero
  refine ⟨W₀, W₁, hW₀ne, hW₀deg, hW₁deg, ?_⟩
  intro i
  have hW₀eval := supportDualPolynomial_eval alpha x₀ halpha i
  have hW₁eval := supportDualPolynomial_eval alpha x₁ halpha i
  change W₀.eval (alpha i) * sigma (E i) =
    W₁.eval (alpha i) * E i
  rw [show W₀.eval (alpha i) =
      x₀ i * supportCoweight alpha i by simpa [W₀] using hW₀eval,
    show W₁.eval (alpha i) =
      x₁ i * supportCoweight alpha i by simpa [W₁] using hW₁eval]
  dsimp [x₀, x₁]
  ring

/-- Smallest end-to-end deterministic failure theorem for the concrete
two-lane syndrome matrix.  Its strict-rank hypothesis is relative to the
*actual support size* `e`, not to the proposed locator width `cols`.
This is precisely what excludes the automatic support-locator kernel. -/
theorem exists_failureRelation_of_rank_lt_actualSupport
    {F : Type*} [Field F] {e rows cols : Nat}
    (sigma : F →+* F) (alpha E weight : Fin e → F)
    (halpha : Function.Injective alpha) (hrows : rows < e)
    (hecols : e ≤ cols)
    (hweight : ∀ i, weight i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank :
      (twoLaneSupportSyndromeMatrix rows rows cols alpha
        (fun i => weight i * E i)
        (fun i => weight i * sigma (E i))).rank < e) :
    ∃ W₀ W₁ : Polynomial F,
      W₀ ≠ 0 ∧
      W₀.natDegree < e - rows ∧
      W₁.natDegree < e - rows ∧
      TwoLaneFailureRelation sigma alpha E W₀ W₁ := by
  obtain ⟨v, hv, hker⟩ :=
    exists_nonzero_supportKernel_of_rank_lt_support
      rows rows alpha
      (fun i => weight i * E i)
      (fun i => weight i * sigma (E i))
      halpha hecols hrank
  exact exists_failureRelation_of_nonzero_supportKernel
    sigma alpha E weight v halpha hrows hweight hE hv hker

/-- If the proposed locator width exceeds the actual error weight, rank
deficiency is automatic and contains no information about the relation
between the two error-value lanes. -/
theorem twoLaneSupportSyndromeMatrix_rank_lt_cols_of_support_lt
    {F : Type*} [Field F] {e : Nat}
    (rows₀ rows₁ cols : Nat) (alpha d₀ d₁ : Fin e → F)
    (he : e < cols) :
    (twoLaneSupportSyndromeMatrix rows₀ rows₁ cols alpha d₀ d₁).rank < cols :=
  (twoLaneSupportSyndromeMatrix_rank_le_support
    rows₀ rows₁ cols alpha d₀ d₁).trans_lt he

/-- Literal score-64.01 specialization: every owner with at most `76789`
actual errors makes the fixed `76790`-column two-lane system deficient,
without using Frobenius at all. -/
theorem benchmark_twoLane_rank_lt_target_of_support_lt6401
    {F : Type*} [Field F] {e : Nat}
    (alpha d₀ d₁ : Fin e → F)
    (he : e < keyErrors6401) :
    (twoLaneSupportSyndromeMatrix
      keyFirstLaneRows6401 keyFirstLaneRows6401 keyErrors6401
      alpha d₀ d₁).rank < keyErrors6401 :=
  twoLaneSupportSyndromeMatrix_rank_lt_cols_of_support_lt
    keyFirstLaneRows6401 keyFirstLaneRows6401 keyErrors6401
    alpha d₀ d₁ he

theorem one_below_target_is_automatic_defect6401 :
    keyErrors6401 - 1 = 76789 ∧ keyErrors6401 - 1 < keyErrors6401 := by
  norm_num [keyErrors6401, bchksErrors6401]

/-! ## Generic-rank minor degree ledger -/

/-- Best row-sensitive degree cap for a rank-`ρ` minor once the ordinary
lane contributes its full possible `min ρ 54282` independent rows. -/
def genericRankMinorDegreeCap6401 (ρ : Nat) : Nat :=
  min ρ keyFirstLaneRows6401 +
    (ρ - keyFirstLaneRows6401) * q6401

theorem genericRankMinorDegreeCap_piecewise6401 (ρ : Nat) :
    (ρ ≤ keyFirstLaneRows6401 →
      genericRankMinorDegreeCap6401 ρ = ρ) ∧
    (keyFirstLaneRows6401 ≤ ρ →
      genericRankMinorDegreeCap6401 ρ =
        keyFirstLaneRows6401 +
          (ρ - keyFirstLaneRows6401) * q6401) := by
  constructor
  · intro h
    simp [genericRankMinorDegreeCap6401, Nat.min_eq_left h,
      Nat.sub_eq_zero_of_le h]
  · intro h
    simp [genericRankMinorDegreeCap6401, Nat.min_eq_right h]

theorem genericRankMinorDegreeCap_target6401 :
    genericRankMinorDegreeCap6401 keyErrors6401 =
      keyMinorDegreeCap6401 := by
  norm_num [genericRankMinorDegreeCap6401, keyMinorDegreeCap6401,
    keyFirstLaneRows6401, keySecondLaneRows6401, keyRedundancy6401,
    keyErrors6401, q6401, n6401, ownerDegreeCap6401, bchksErrors6401]

theorem genericRankMinorDegreeCap_le_target6401
    (ρ : Nat) (hρ : ρ ≤ keyErrors6401) :
    genericRankMinorDegreeCap6401 ρ ≤ keyMinorDegreeCap6401 := by
  norm_num [genericRankMinorDegreeCap6401, keyMinorDegreeCap6401,
    keyFirstLaneRows6401, keySecondLaneRows6401, keyRedundancy6401,
    keyErrors6401, q6401, n6401, ownerDegreeCap6401,
    bchksErrors6401] at hρ ⊢
  omega

/-- In the strict branch with actual support `s`, each shortened-dual
polynomial has degree at most `s - 54282 - 1`.  Since `s ≤ 76790`, this is
always at most the sharp primitive cap `22507`. -/
def supportFailureDegreeCap6401 (s : Nat) : Nat :=
  s - keyFirstLaneRows6401 - 1

theorem supportFailureDegreeCap_le_22507
    (s : Nat) (hs : s ≤ keyErrors6401) :
    supportFailureDegreeCap6401 s ≤ 22507 := by
  norm_num [supportFailureDegreeCap6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401, n6401,
    ownerDegreeCap6401, bchksErrors6401] at hs ⊢
  omega

/-- Even the crude all-Frobenius degree bound for an arbitrary generic-rank
minor is far below the weak-seed challenge count.  This permits finding one
generic-rank specialization with an owner first; at that specialization the
ordinary block has rank `min ρ 54282`, yielding the sharper cap above. -/
theorem crudeGenericMinorCap_lt_weakInput6401
    (ρ : Nat) (hρ : ρ ≤ keyErrors6401) :
    ρ * q6401 < weakCurveSeedInput6401 := by
  norm_num [keyErrors6401, bchksErrors6401, q6401,
    weakCurveSeedInput6401,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401, n6401, wideListBound] at hρ ⊢
  omega

end BCHKSFrobeniusRectangularHankelAudit6401
end ProximityPrize.SubmissionLower

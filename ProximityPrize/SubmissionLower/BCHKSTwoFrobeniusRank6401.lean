import ProximityPrize.SubmissionLower.BCHKSParameters6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRank6401
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
def domainSize : ℕ := 262144
def agreementSize : ℕ := 185354
def messageDegree : ℕ := 131071
def constantWidth : ℕ := 174763
def semilinearWidth : ℕ := 43692
def variableCount : ℕ := constantWidth + 2 * semilinearWidth
theorem concrete_counts6401 :
    variableCount = 262147 ∧
      domainSize = 262144 ∧
      variableCount = domainSize + 3 ∧
      agreementSize = 185354 ∧
      messageDegree = 131071 ∧
      (constantWidth - 1) = 174762 ∧
      (semilinearWidth - 1) + messageDegree = 174762 ∧
      174762 < agreementSize := by
  norm_num [variableCount, domainSize, agreementSize, messageDegree,
    constantWidth, semilinearWidth]
abbrev BoundedTriple (K : Type*) [Field K] :=
  Polynomial.degreeLT K constantWidth ×
    Polynomial.degreeLT K semilinearWidth ×
      Polynomial.degreeLT K semilinearWidth
def component {K : Type*} [Field K]
    (q : BoundedTriple K) : Fin 3 → Polynomial K :=
  ![(q.1 : Polynomial K), (q.2.1 : Polynomial K),
    (q.2.2 : Polynomial K)]
noncomputable def twist {K : Type*} [Field K] (sigma : K →+* K)
    (P : Polynomial K) : Polynomial K :=
  P.map sigma
noncomputable def relationPolynomial {K : Type*} [Field K] (sigma : K →+* K)
    (q : BoundedTriple K) (P : Polynomial K) : Polynomial K :=
  (q.1 : Polynomial K) + (q.2.1 : Polynomial K) * P +
    (q.2.2 : Polynomial K) * twist sigma P
noncomputable def interpolationMap {K : Type*} [Field K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K) :
    BoundedTriple K →ₗ[K] (Fin domainSize → K) where
  toFun q i :=
    Polynomial.eval (alpha i) (q.1 : Polynomial K) +
      Polynomial.eval (alpha i) (q.2.1 : Polynomial K) * received i +
      Polynomial.eval (alpha i) (q.2.2 : Polynomial K) * sigma (received i)
  map_add' q r := by
    funext i
    simp
    ring
  map_smul' c q := by
    funext i
    simp
    ring
noncomputable abbrev InterpolationKernel {K : Type*} [Field K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K) :=
  LinearMap.ker (interpolationMap sigma alpha received)
theorem boundedTriple_finrank {K : Type*} [Field K] :
    Module.finrank K (BoundedTriple K) = variableCount := by
  rw [Module.finrank_prod, Module.finrank_prod,
    LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv K constantWidth),
    LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv K semilinearWidth)]
  simp [variableCount, two_mul]
theorem interpolationTarget_finrank {K : Type*} [Field K] :
    Module.finrank K (Fin domainSize → K) = domainSize := by
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
theorem interpolationKernel_finrank_ge_three
    {K : Type*} [Field K] (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K) (received : Fin domainSize → K) :
    3 ≤ Module.finrank K (InterpolationKernel sigma alpha received) := by
  change 3 ≤ Module.finrank K
    (LinearMap.ker (interpolationMap sigma alpha received))
  have hrange : Module.finrank K
      (LinearMap.range (interpolationMap sigma alpha received)) ≤ domainSize := by
    calc
      Module.finrank K
          (LinearMap.range (interpolationMap sigma alpha received)) ≤
          Module.finrank K (Fin domainSize → K) := Submodule.finrank_le _
      _ = domainSize := interpolationTarget_finrank
  have hranknull := LinearMap.finrank_range_add_finrank_ker
    (interpolationMap sigma alpha received)
  rw [boundedTriple_finrank, concrete_counts6401.1] at hranknull
  norm_num [domainSize] at hrange
  omega
theorem exists_three_independent_kernel_rows
    {K : Type*} [Field K] (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K) (received : Fin domainSize → K) :
    ∃ q : Fin 3 → InterpolationKernel sigma alpha received,
      LinearIndependent K q :=
  exists_linearIndependent_of_le_finrank
    (interpolationKernel_finrank_ge_three sigma alpha received)
theorem eval_twist_of_fixed {K : Type*} [Field K]
    (sigma : K →+* K) (x : K) (hx : sigma x = x)
    (P : Polynomial K) :
    Polynomial.eval x (twist sigma P) = sigma (Polynomial.eval x P) := by
  simpa [twist, hx] using
    (Polynomial.eval_map_apply (p := P) sigma x)
def EvaluatesToReceived {K : Type*} [Field K]
    (alpha : Fin domainSize ↪ K) (received : Fin domainSize → K)
    (A : Finset (Fin domainSize)) (P : Polynomial K) : Prop :=
  ∀ i ∈ A, Polynomial.eval (alpha i) P = received i
theorem kernel_evaluation_relation {K : Type*} [Field K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K)
    (q : InterpolationKernel sigma alpha received) (i : Fin domainSize) :
    Polynomial.eval (alpha i) (q.1.1 : Polynomial K) +
      Polynomial.eval (alpha i) (q.1.2.1 : Polynomial K) * received i +
      Polynomial.eval (alpha i) (q.1.2.2 : Polynomial K) *
        sigma (received i) = 0 := by
  have h := congrFun q.2 i
  change Polynomial.eval (alpha i) (q.1.1 : Polynomial K) +
      Polynomial.eval (alpha i) (q.1.2.1 : Polynomial K) * received i +
      Polynomial.eval (alpha i) (q.1.2.2 : Polynomial K) *
        sigma (received i) = 0 at h
  exact h
private theorem natDegree_lt_width {K : Type*} [Field K]
    {w : ℕ} (hw : 0 < w) (P : Polynomial.degreeLT K w) :
    (P : Polynomial K).natDegree < w := by
  by_cases hP : (P : Polynomial K) = 0
  · simp [hP, hw]
  · exact (Polynomial.natDegree_lt_iff_degree_lt hP).2
      (Polynomial.mem_degreeLT.mp P.2)
theorem relationPolynomial_natDegree_le {K : Type*} [Field K]
    (sigma : K →+* K) (q : BoundedTriple K) (P : Polynomial K)
    (hP : P.natDegree ≤ messageDegree) :
    (relationPolynomial sigma q P).natDegree ≤ 174762 := by
  have h0 : (q.1 : Polynomial K).natDegree ≤ 174762 := by
    have := natDegree_lt_width (K := K) (w := constantWidth) (by norm_num [constantWidth]) q.1
    norm_num [constantWidth] at this
    omega
  have h1c : (q.2.1 : Polynomial K).natDegree ≤ 43691 := by
    have := natDegree_lt_width (K := K) (w := semilinearWidth)
      (by norm_num [semilinearWidth]) q.2.1
    norm_num [semilinearWidth] at this
    omega
  have h2c : (q.2.2 : Polynomial K).natDegree ≤ 43691 := by
    have := natDegree_lt_width (K := K) (w := semilinearWidth)
      (by norm_num [semilinearWidth]) q.2.2
    norm_num [semilinearWidth] at this
    omega
  have h1 : ((q.2.1 : Polynomial K) * P).natDegree ≤ 174762 :=
    Polynomial.natDegree_mul_le.trans (by
      norm_num [messageDegree] at hP ⊢
      omega)
  have hsigma : (twist sigma P).natDegree ≤ messageDegree := by
    exact Polynomial.natDegree_map_le.trans hP
  have h2 : ((q.2.2 : Polynomial K) * twist sigma P).natDegree ≤ 174762 :=
    Polynomial.natDegree_mul_le.trans (by
      norm_num [messageDegree] at hsigma ⊢
      omega)
  unfold relationPolynomial
  exact (Polynomial.natDegree_add_le _ _).trans <| max_le
    ((Polynomial.natDegree_add_le _ _).trans (max_le h0 h1)) h2
theorem relationPolynomial_eq_zero_of_owner
    {K : Type*} [Field K] [DecidableEq K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : InterpolationKernel sigma alpha received)
    (A : Finset (Fin domainSize)) (P : Polynomial K)
    (hP : P.natDegree ≤ messageDegree)
    (howner : EvaluatesToReceived alpha received A P)
    (hcard : 174762 < A.card) :
    relationPolynomial sigma q.1 P = 0 := by
  let roots : Finset K := A.map alpha
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (relationPolynomial sigma q.1 P) roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hrow := kernel_evaluation_relation sigma alpha received q i
    have hown := howner i hi
    have htwist := eval_twist_of_fixed sigma (alpha i) (hfixed i) P
    simp only [relationPolynomial, Polynomial.eval_add, Polynomial.eval_mul]
    rw [hown, htwist, hown]
    exact hrow
  · rw [Finset.card_map]
    exact (relationPolynomial_natDegree_le sigma q.1 P hP).trans_lt hcard
theorem relationPolynomial_eq_zero_of_benchmark_owner
    {K : Type*} [Field K] [DecidableEq K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : InterpolationKernel sigma alpha received)
    (A : Finset (Fin domainSize)) (P : Polynomial K)
    (hP : P.natDegree ≤ messageDegree)
    (howner : EvaluatesToReceived alpha received A P)
    (hcard : agreementSize ≤ A.card) :
    relationPolynomial sigma q.1 P = 0 := by
  apply relationPolynomial_eq_zero_of_owner sigma alpha received hfixed
      q A P hP howner
  have := concrete_counts6401.2.2.2.2.2.2.2
  omega
def rowMatrix {K : Type*} [Field K]
    (q : Fin 3 → BoundedTriple K) : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
  fun i => component (q i)
noncomputable def ownerVector {K : Type*} [Field K] (sigma : K →+* K)
    (P : Polynomial K) : Fin 3 → Polynomial K :=
  ![1, P, twist sigma P]
theorem rowMatrix_mulVec_owner_apply {K : Type*} [Field K]
    (sigma : K →+* K) (q : Fin 3 → BoundedTriple K)
    (P : Polynomial K) (i : Fin 3) :
    (rowMatrix q).mulVec (ownerVector sigma P) i =
      relationPolynomial sigma (q i) P := by
  simp [rowMatrix, component, ownerVector, relationPolynomial,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem selected_kernel_rows_det_eq_zero_of_owner
    {K : Type*} [Field K] [DecidableEq K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : Fin 3 → InterpolationKernel sigma alpha received)
    (A : Finset (Fin domainSize)) (P : Polynomial K)
    (hP : P.natDegree ≤ messageDegree)
    (howner : EvaluatesToReceived alpha received A P)
    (hcard : agreementSize ≤ A.card) :
    (rowMatrix (fun i => (q i).1)).det = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (i := (0 : Fin 3))
  · funext i
    rw [rowMatrix_mulVec_owner_apply]
    exact relationPolynomial_eq_zero_of_benchmark_owner
      sigma alpha received hfixed (q i) A P hP howner hcard
  · exact mem_nonZeroDivisors_of_ne_zero (by simp [ownerVector])
theorem no_benchmark_owner_of_selected_det_ne_zero
    {K : Type*} [Field K] [DecidableEq K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : Fin 3 → InterpolationKernel sigma alpha received)
    (hdet : (rowMatrix (fun i => (q i).1)).det ≠ 0)
    (A : Finset (Fin domainSize)) (P : Polynomial K)
    (hP : P.natDegree ≤ messageDegree)
    (hcard : agreementSize ≤ A.card) :
    ¬ EvaluatesToReceived alpha received A P := by
  intro howner
  exact hdet (selected_kernel_rows_det_eq_zero_of_owner sigma alpha received
    hfixed q A P hP howner hcard)
noncomputable def minor01 {K : Type*} [Field K]
    (q r : BoundedTriple K) : Polynomial K :=
  (q.1 : Polynomial K) * (r.2.1 : Polynomial K) -
    (r.1 : Polynomial K) * (q.2.1 : Polynomial K)
noncomputable def rankTwoNumerator {K : Type*} [Field K]
    (q r : BoundedTriple K) : Polynomial K :=
  (q.1 : Polynomial K) * (r.2.2 : Polynomial K) -
    (r.1 : Polynomial K) * (q.2.2 : Polynomial K)
noncomputable def rankTwoDenominator {K : Type*} [Field K]
    (q r : BoundedTriple K) : Polynomial K :=
  (q.2.1 : Polynomial K) * (r.2.2 : Polynomial K) -
    (r.2.1 : Polynomial K) * (q.2.2 : Polynomial K)
def RowPairIndependent {K : Type*} [Field K]
    (q r : BoundedTriple K) : Prop :=
  minor01 q r ≠ 0 ∨ rankTwoNumerator q r ≠ 0 ∨
    rankTwoDenominator q r ≠ 0
theorem rankTwo_polynomial_identity {K : Type*} [Field K]
    (sigma : K →+* K) (q r : BoundedTriple K) (P : Polynomial K)
    (hq : relationPolynomial sigma q P = 0)
    (hr : relationPolynomial sigma r P = 0) :
    rankTwoDenominator q r * P = -rankTwoNumerator q r := by
  unfold relationPolynomial rankTwoDenominator rankTwoNumerator at *
  linear_combination
    (r.2.2 : Polynomial K) * hq - (q.2.2 : Polynomial K) * hr
theorem minor01_eq_zero_of_denominator_eq_zero {K : Type*} [Field K]
    (sigma : K →+* K) (q r : BoundedTriple K) (P : Polynomial K)
    (hq : relationPolynomial sigma q P = 0)
    (hr : relationPolynomial sigma r P = 0)
    (hden : rankTwoDenominator q r = 0) :
    minor01 q r = 0 := by
  unfold relationPolynomial rankTwoDenominator minor01 at *
  linear_combination
    (r.2.1 : Polynomial K) * hq - (q.2.1 : Polynomial K) * hr +
      twist sigma P * hden
theorem rankTwoDenominator_ne_zero_of_independent {K : Type*} [Field K]
    (sigma : K →+* K) (q r : BoundedTriple K) (P : Polynomial K)
    (hq : relationPolynomial sigma q P = 0)
    (hr : relationPolynomial sigma r P = 0)
    (hind : RowPairIndependent q r) :
    rankTwoDenominator q r ≠ 0 := by
  intro hden
  have hnum : rankTwoNumerator q r = 0 := by
    have h := rankTwo_polynomial_identity sigma q r P hq hr
    rw [hden, zero_mul] at h
    exact neg_eq_zero.mp h.symm
  have h01 := minor01_eq_zero_of_denominator_eq_zero sigma q r P hq hr hden
  exact hind.elim (fun h => h h01) (fun h => h.elim (fun hn => hn hnum)
    (fun hd => hd hden))
theorem rankTwo_owner_unique {K : Type*} [Field K]
    (q r : BoundedTriple K) (P Q : Polynomial K)
    (hden : rankTwoDenominator q r ≠ 0)
    (hP : rankTwoDenominator q r * P = -rankTwoNumerator q r)
    (hQ : rankTwoDenominator q r * Q = -rankTwoNumerator q r) :
    P = Q := by
  apply mul_left_cancel₀ hden
  exact hP.trans hQ.symm
theorem rankTwo_fraction_formula {K : Type*} [Field K]
    (q r : BoundedTriple K) (P : Polynomial K)
    (hden : rankTwoDenominator q r ≠ 0)
    (hP : rankTwoDenominator q r * P = -rankTwoNumerator q r) :
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) P =
      -algebraMap (Polynomial K) (FractionRing (Polynomial K))
          (rankTwoNumerator q r) /
        algebraMap (Polynomial K) (FractionRing (Polynomial K))
          (rankTwoDenominator q r) := by
  let phi := algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have hden' : phi (rankTwoDenominator q r) ≠ 0 :=
    by simpa [phi] using
      (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))).ne hden
  apply (eq_div_iff hden').2
  have hmapped := congrArg phi hP
  simpa [phi, map_mul, map_neg, mul_comm] using hmapped
theorem independent_pair_gives_fraction_formula {K : Type*} [Field K]
    (sigma : K →+* K) (q r : BoundedTriple K) (P : Polynomial K)
    (hq : relationPolynomial sigma q P = 0)
    (hr : relationPolynomial sigma r P = 0)
    (hind : RowPairIndependent q r) :
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) P =
      -algebraMap (Polynomial K) (FractionRing (Polynomial K))
          (rankTwoNumerator q r) /
        algebraMap (Polynomial K) (FractionRing (Polynomial K))
          (rankTwoDenominator q r) := by
  apply rankTwo_fraction_formula q r P
  · exact rankTwoDenominator_ne_zero_of_independent sigma q r P hq hr hind
  · exact rankTwo_polynomial_identity sigma q r P hq hr
theorem independent_kernel_pair_gives_fraction_formula_of_owner
    {K : Type*} [Field K] [DecidableEq K]
    (sigma : K →+* K) (alpha : Fin domainSize ↪ K)
    (received : Fin domainSize → K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q r : InterpolationKernel sigma alpha received)
    (hind : RowPairIndependent q.1 r.1)
    (A : Finset (Fin domainSize)) (P : Polynomial K)
    (hP : P.natDegree ≤ messageDegree)
    (howner : EvaluatesToReceived alpha received A P)
    (hcard : agreementSize ≤ A.card) :
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) P =
      -algebraMap (Polynomial K) (FractionRing (Polynomial K))
          (rankTwoNumerator q.1 r.1) /
        algebraMap (Polynomial K) (FractionRing (Polynomial K))
          (rankTwoDenominator q.1 r.1) := by
  apply independent_pair_gives_fraction_formula sigma q.1 r.1 P
  · exact relationPolynomial_eq_zero_of_benchmark_owner sigma alpha received
      hfixed q A P hP howner hcard
  · exact relationPolynomial_eq_zero_of_benchmark_owner sigma alpha received
      hfixed r A P hP howner hcard
  · exact hind
def DenominatorSpecializationControl
    {R E ι : Type*} [CommRing R] [Field E] [DecidableEq ι]
    (specialize : ι → R →+* E) (denominator : R) : Prop :=
  ∃ bad : Finset ι, ∀ z ∉ bad, specialize z denominator ≠ 0
def IsAffinePolynomialFamily
    {E ι : Type*} [Field E] (zValue : ι → E)
    (P : ι → Polynomial E) : Prop :=
  ∃ P₀ P₁ : Polynomial E, ∀ z,
    P z = P₀ + Polynomial.C (zValue z) * P₁
def PolynomialSpecializationDescent
    {R E ι : Type*} [CommRing R] [Field E]
    (specialize : ι → R →+* Polynomial E)
    (zValue : ι → E) (good : Finset ι)
    (numerator denominator : R) (degreeCap : ℕ) : Prop :=
  ∀ P : ι → Polynomial E,
    (∀ z ∈ good,
      (P z).natDegree ≤ degreeCap ∧
      specialize z denominator * P z = -specialize z numerator) →
    IsAffinePolynomialFamily zValue P
theorem affine_of_polynomialSpecializationDescent
    {R E ι : Type*} [CommRing R] [Field E]
    (specialize : ι → R →+* Polynomial E)
    (zValue : ι → E) (good : Finset ι)
    (numerator denominator : R) (degreeCap : ℕ)
    (hdescent : PolynomialSpecializationDescent specialize zValue good
      numerator denominator degreeCap)
    (P : ι → Polynomial E)
    (hP : ∀ z ∈ good,
      (P z).natDegree ≤ degreeCap ∧
      specialize z denominator * P z = -specialize z numerator) :
    IsAffinePolynomialFamily zValue P :=
  hdescent P hP
theorem exists_direction_projection_of_affine_owner_alignment
    {ι E : Type} [Fintype ι] [DecidableEq ι] [Field E] [DecidableEq E]
    (C : LinearCode ι E) (U p : Fin 2 → ι → E)
    (S : Finset E) (T : E → Finset ι) (errors : ℕ)
    (hS : errors + 1 < S.card)
    (hTcard : ∀ z ∈ S, Fintype.card ι - errors ≤ (T z).card)
    (hpC : ∀ j, p j ∈ C)
    (halign : ∀ z ∈ S, ∀ i ∈ T z,
      U 0 i + z * U 1 i = p 0 i + z * p 1 i) :
    ∃ z ∈ S, LinearCode.projectedWord (U 1) (T z) ∈
      LinearCode.projectedCodeSubmod C (T z) := by
  obtain ⟨z, hzS, hz⟩ :=
    @exists_common_affine_set ι E _ _ _ _ U p S T errors hS hTcard halign
  refine ⟨z, hzS, ?_⟩
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨p 1, hpC 1, ?_⟩
  funext i
  exact (hz i.1 i.2).2
def RankOnePeriodicBranch {K : Type*} [Field K]
    (V : Submodule K (BoundedTriple K)) : Prop :=
  ∀ q ∈ V, ∀ r ∈ V, ¬ RowPairIndependent q r
theorem rankTwo_or_rankOnePeriodic {K : Type*} [Field K]
    (V : Submodule K (BoundedTriple K)) :
    (∃ q ∈ V, ∃ r ∈ V, RowPairIndependent q r) ∨
      RankOnePeriodicBranch V := by
  classical
  by_cases h : ∃ q ∈ V, ∃ r ∈ V, RowPairIndependent q r
  · exact Or.inl h
  · right
    intro q hq r hr hind
    exact h ⟨q, hq, r, hr, hind⟩
noncomputable def universalPeriodicRow {K : Type*} [Field K] :
    BoundedTriple K :=
  (⟨0, by simp [constantWidth]⟩,
    ⟨1, Polynomial.mem_degreeLT.mpr (by simp [semilinearWidth])⟩,
    ⟨-1, Polynomial.mem_degreeLT.mpr (by simp [semilinearWidth])⟩)
theorem universalPeriodicRow_annihilates_fixed_polynomial
    {K : Type*} [Field K] (sigma : K →+* K) (P : Polynomial K)
    (hfixed : twist sigma P = P) :
    relationPolynomial sigma (universalPeriodicRow (K := K)) P = 0 := by
  simp [relationPolynomial, universalPeriodicRow, hfixed]
theorem universalPeriodicRow_mem_kernel_of_received_fixed
    {K : Type*} [Field K] (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K) (received : Fin domainSize → K)
    (hreceived : ∀ i, sigma (received i) = received i) :
    universalPeriodicRow (K := K) ∈
      InterpolationKernel sigma alpha received := by
  ext i
  simp [interpolationMap, universalPeriodicRow, hreceived i]
end BCHKSTwoFrobeniusRank6401
end ProximityPrize.SubmissionLower

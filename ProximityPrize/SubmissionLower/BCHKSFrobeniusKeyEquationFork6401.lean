import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusWeakCurveSeed6401
import ProximityPrize.SubmissionLower.BCHKSGaoSpecializationCore6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusKeyEquationFork6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSGaoSpecializationCore6400
open BCHKSSphericalL3Radius76855Audit6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
def keyRedundancy6401 : Nat := n6401 - (ownerDegreeCap6401 + 1)
def keyErrors6401 : Nat := bchksErrors6401
def keyFirstLaneRows6401 : Nat := keyRedundancy6401 - keyErrors6401
def keySecondLaneRows6401 : Nat :=
  keyErrors6401 - keyFirstLaneRows6401
abbrev KeyMinorRow6401 :=
  Fin keyFirstLaneRows6401 ⊕ Fin keySecondLaneRows6401
def keyMinorRowCap6401 : KeyMinorRow6401 → Nat
  | Sum.inl _ => 1
  | Sum.inr _ => q6401
def keyMinorDegreeCap6401 : Nat :=
  keyFirstLaneRows6401 + keySecondLaneRows6401 * q6401
def keyGoodChallengeFloor6401 : Nat :=
  weakCurveSeedInput6401 - keyMinorDegreeCap6401
def keyVariableErrorCap6401 : Nat := 32
theorem keyEquation_parameters_exact6401 :
    keyRedundancy6401 = 131072 ∧
      keyErrors6401 = 76790 ∧
      keyFirstLaneRows6401 = 54282 ∧
      keySecondLaneRows6401 = 22508 ∧
      keyFirstLaneRows6401 + keySecondLaneRows6401 = keyErrors6401 ∧
      Fintype.card KeyMinorRow6401 = keyErrors6401 ∧
      keyMinorDegreeCap6401 = 47957940448246 ∧
      keyGoodChallengeFloor6401 = 273543241402362822 := by
  norm_num [keyRedundancy6401, keyErrors6401, keyFirstLaneRows6401,
    keySecondLaneRows6401, keyMinorDegreeCap6401,
    keyGoodChallengeFloor6401, weakCurveSeedInput6401,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401, n6401, ownerDegreeCap6401,
    bchksErrors6401, wideListBound, q6401, Fintype.card_fin]
theorem keyMinorRowCap_sum_exact6401 :
    ∑ i : KeyMinorRow6401, keyMinorRowCap6401 i =
      keyMinorDegreeCap6401 := by
  rw [Fintype.sum_sum_type]
  simp only [keyMinorRowCap6401, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num [keyMinorDegreeCap6401,
    keyFirstLaneRows6401, keySecondLaneRows6401, keyRedundancy6401,
    keyErrors6401, n6401, ownerDegreeCap6401, bchksErrors6401,
    q6401]
noncomputable def syndromeWeight
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha : ι → F) (i : ι) : F :=
  Lagrange.nodalWeight Finset.univ alpha i
noncomputable def weightedSyndrome
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha y : ι → F) (j : Nat) : F :=
  ∑ i, syndromeWeight alpha i * alpha i ^ j * y i
def supportSyndrome
    {F : Type*} [Field F] {t : Nat}
    (alpha d : Fin t → F) (j : Nat) : F :=
  ∑ i, d i * alpha i ^ j
def supportSyndromeMatrix
    {F : Type*} [Field F] {t : Nat}
    (rows cols : Nat) (alpha d : Fin t → F) :
    Matrix (Fin rows) (Fin cols) F :=
  fun i j => supportSyndrome alpha d (i.1 + j.1)
def syndromeLeftVandermonde
    {F : Type*} [Field F] {t rows : Nat} (alpha : Fin t → F) :
    Matrix (Fin rows) (Fin t) F :=
  fun i j => alpha j ^ i.1
def syndromeRightVandermonde
    {F : Type*} [Field F] {t : Nat} (alpha : Fin t → F) :
    Matrix (Fin t) (Fin t) F :=
  fun i j => alpha i ^ j.1
theorem supportSyndromeMatrix_factorization
    {F : Type*} [Field F] {t rows : Nat} (alpha d : Fin t → F) :
    supportSyndromeMatrix rows t alpha d =
      syndromeLeftVandermonde alpha * Matrix.diagonal d *
        syndromeRightVandermonde alpha := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  simp only [supportSyndromeMatrix, supportSyndrome,
    syndromeLeftVandermonde, syndromeRightVandermonde]
  apply Finset.sum_congr rfl
  intro x hx
  simp [pow_add, mul_assoc, mul_comm]
theorem supportSyndromeMatrix_rank_eq_min
    {F : Type*} [Field F] {t rows : Nat} (alpha d : Fin t → F)
    (halpha : Function.Injective alpha) (hd : ∀ i, d i ≠ 0) :
    (supportSyndromeMatrix rows t alpha d).rank = min rows t := by
  classical
  rw [supportSyndromeMatrix_factorization]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det]
    · rw [show syndromeLeftVandermonde alpha =
          (Vandermonde.nonsquare rows alpha).transpose by rfl,
        Matrix.rank_transpose,
        Vandermonde.rank_nonsquare_rows_eq_min halpha,
        Nat.min_comm]
    · rw [Matrix.det_diagonal]
      exact isUnit_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  · rw [show syndromeRightVandermonde alpha =
        Matrix.vandermonde alpha by rfl]
    exact isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr halpha)
theorem supportSyndromeMatrix_rank_eq_rows
    {F : Type*} [Field F] {t rows : Nat} (alpha d : Fin t → F)
    (halpha : Function.Injective alpha) (hd : ∀ i, d i ≠ 0)
    (hrows : rows ≤ t) :
    (supportSyndromeMatrix rows t alpha d).rank = rows := by
  rw [supportSyndromeMatrix_rank_eq_min alpha d halpha hd,
    Nat.min_eq_left hrows]
noncomputable def locatorPolynomial
    {F : Type*} [Field F] {t : Nat} (c : Fin t → F) : F[X] :=
  (Polynomial.X : F[X]) ^ t +
    ∑ j, Polynomial.monomial j.1 (c j)
theorem eval_locatorPolynomial
    {F : Type*} [Field F] {t : Nat} (c : Fin t → F) (x : F) :
    (locatorPolynomial c).eval x = x ^ t + ∑ j, c j * x ^ j.1 := by
  classical
  simp [locatorPolynomial, Polynomial.eval_finsetSum]
def supportKeyRhs
    {F : Type*} [Field F] {t rows : Nat} (alpha d : Fin t → F) :
    Fin rows → F :=
  fun i => -supportSyndrome alpha d (i.1 + t)
theorem locator_keyEquation
    {F : Type*} [Field F] {t rows : Nat} (alpha d : Fin t → F)
    (c : Fin t → F)
    (hroot : ∀ i, (locatorPolynomial c).eval (alpha i) = 0) :
    (supportSyndromeMatrix rows t alpha d).mulVec c =
      supportKeyRhs alpha d := by
  funext r
  simp only [supportSyndromeMatrix, Matrix.mulVec, dotProduct,
    supportSyndrome, supportKeyRhs]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hri := hroot i
  rw [eval_locatorPolynomial] at hri
  rw [show (∑ x : Fin t,
        d i * alpha i ^ (r.1 + x.1) * c x) =
      d i * alpha i ^ r.1 *
        (∑ x : Fin t, c x * alpha i ^ x.1) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp [pow_add, mul_assoc, mul_left_comm, mul_comm]]
  rw [show ∑ x : Fin t, c x * alpha i ^ x.1 = -(alpha i ^ t) by
    linear_combination hri]
  simp [pow_add, mul_assoc]
theorem weightedSyndrome_codeword_eq_zero
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha : ι ↪ F) (P : F[X]) (j : Nat)
    (hdeg : P.natDegree + j < Fintype.card ι - 1) :
    weightedSyndrome alpha (fun i => P.eval (alpha i)) j = 0 := by
  classical
  let Q : F[X] := P * (Polynomial.X : F[X]) ^ j
  have hnQ : Q.natDegree < Fintype.card ι - 1 := by
    exact lt_of_le_of_lt Polynomial.natDegree_mul_le
      (by simpa [Q] using hdeg)
  have hnQcard : Q.natDegree < Fintype.card ι := by omega
  have hdegree : Q.degree < (Fintype.card ι : WithBot Nat) := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hQ).mp hnQcard
  have hc := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset ι)) (v := fun i => alpha i)
    alpha.injective.injOn hdegree
  have hcoeff : Q.coeff (Fintype.card ι - 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hnQ
  have hc' : (∑ i : ι, Q.eval (alpha i) /
      ∏ j ∈ (Finset.univ : Finset ι).erase i,
        (alpha i - alpha j)) = 0 := by
    rw [← hc]
    simpa using hcoeff
  rw [← hc']
  simp only [weightedSyndrome, syndromeWeight]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Q, Lagrange.nodalWeight, div_eq_mul_inv,
    Finset.prod_inv_distrib, mul_assoc, mul_left_comm, mul_comm]
theorem weightedSyndrome_received_eq_error
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha : ι ↪ F) (P : F[X]) (E u : ι → F) (j : Nat)
    (hu : ∀ i, u i = P.eval (alpha i) + E i)
    (hdeg : P.natDegree + j < Fintype.card ι - 1) :
    weightedSyndrome alpha u j = weightedSyndrome alpha E j := by
  have hzero := weightedSyndrome_codeword_eq_zero alpha P j hdeg
  calc
    weightedSyndrome alpha u j =
        weightedSyndrome alpha (fun i => P.eval (alpha i)) j +
          weightedSyndrome alpha E j := by
      classical
      simp only [weightedSyndrome, hu, mul_add, Finset.sum_add_distrib]
    _ = weightedSyndrome alpha E j := by rw [hzero, zero_add]
theorem syndromeWeight_ne_zero
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha : ι ↪ F) (i : ι) : syndromeWeight alpha i ≠ 0 := by
  exact Lagrange.nodalWeight_ne_zero alpha.injective.injOn
    (Finset.mem_univ i)
theorem benchmark_syndrome_domain_exact6401 :
    Fintype.card ProximityPrize.Benchmark.IRSProfile.Index = n6401 ∧
      Function.Injective ProximityPrize.Benchmark.IRSProfile.domain := by
  constructor
  · norm_num [ProximityPrize.Benchmark.IRSProfile.Index, n6401]
  · exact ProximityPrize.Benchmark.IRSProfile.domain.injective
noncomputable def affineSyndromeZ
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha u₀ u₁ : ι → F) (j : Nat) : F[X] :=
  Polynomial.C (weightedSyndrome alpha u₀ j) +
    Polynomial.X * Polynomial.C (weightedSyndrome alpha u₁ j)
theorem affineSyndromeZ_eval
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha u₀ u₁ : ι → F) (j : Nat) (z : F) :
    (affineSyndromeZ alpha u₀ u₁ j).eval z =
      weightedSyndrome alpha (fun i => u₀ i + z * u₁ i) j := by
  classical
  simp only [affineSyndromeZ, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, weightedSyndrome]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem affineSyndromeZ_natDegree_le_one
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha u₀ u₁ : ι → F) (j : Nat) :
    (affineSyndromeZ alpha u₀ u₁ j).natDegree ≤ 1 := by
  unfold affineSyndromeZ
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)
noncomputable def frobeniusSyndromeZ
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (q : Nat) (alpha u₀ u₁ : ι → F) (j : Nat) : F[X] :=
  Polynomial.C
      (weightedSyndrome alpha (fun i => sigma (u₀ i)) j) +
    Polynomial.monomial q
      (weightedSyndrome alpha (fun i => sigma (u₁ i)) j)
theorem frobeniusSyndromeZ_natDegree_le
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (q : Nat) (alpha u₀ u₁ : ι → F) (j : Nat) :
    (frobeniusSyndromeZ sigma q alpha u₀ u₁ j).natDegree ≤ q := by
  unfold frobeniusSyndromeZ
  apply (Polynomial.natDegree_add_le _ _).trans
  exact max_le (by simp) (Polynomial.natDegree_monomial_le _)
theorem frobeniusSyndromeZ_eval
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (q : Nat) (alpha u₀ u₁ : ι → F)
    (j : Nat) (z : F) (hz : sigma z = z ^ q) :
    (frobeniusSyndromeZ sigma q alpha u₀ u₁ j).eval z =
      weightedSyndrome alpha
        (fun i => sigma (u₀ i + z * u₁ i)) j := by
  classical
  simp only [frobeniusSyndromeZ, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_monomial, weightedSyndrome,
    map_add, map_mul, hz]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem keyMinorRows_add_eq_errors6401 :
    keyFirstLaneRows6401 + keySecondLaneRows6401 = keyErrors6401 := by
  norm_num [keyFirstLaneRows6401, keySecondLaneRows6401,
    keyRedundancy6401, keyErrors6401, n6401, ownerDegreeCap6401,
    bchksErrors6401]
noncomputable def keyMinorColumnEquiv6401 :
    KeyMinorRow6401 ≃ Fin keyErrors6401 :=
  finSumFinEquiv.trans (finCongr keyMinorRows_add_eq_errors6401)
abbrev FullTwoLaneKeyRow6401 :=
  Fin keyFirstLaneRows6401 ⊕ Fin keyFirstLaneRows6401
def fullTwoLaneSupportMatrix6401
    {F : Type*} [Field F]
    (alpha d₀ d₁ : Fin keyErrors6401 → F) :
    Matrix FullTwoLaneKeyRow6401 (Fin keyErrors6401) F :=
  fun row col =>
    match row with
    | Sum.inl a => supportSyndrome alpha d₀ (a.1 + col.1)
    | Sum.inr a => supportSyndrome alpha d₁ (a.1 + col.1)
theorem fullTwoLaneSupportMatrix_ordinaryBlock6401
    {F : Type*} [Field F]
    (alpha d₀ d₁ : Fin keyErrors6401 → F) :
    (fullTwoLaneSupportMatrix6401 alpha d₀ d₁).submatrix Sum.inl id =
      supportSyndromeMatrix keyFirstLaneRows6401 keyErrors6401
        alpha d₀ := by
  rfl
theorem fullTwoLaneSupportMatrix_ordinary_rank6401
    {F : Type*} [Field F]
    (alpha d₀ d₁ : Fin keyErrors6401 → F)
    (halpha : Function.Injective alpha) (hd₀ : ∀ i, d₀ i ≠ 0) :
    ((fullTwoLaneSupportMatrix6401 alpha d₀ d₁).submatrix
      Sum.inl id).rank = keyFirstLaneRows6401 := by
  rw [fullTwoLaneSupportMatrix_ordinaryBlock6401]
  apply supportSyndromeMatrix_rank_eq_rows alpha d₀ halpha hd₀
  norm_num [keyFirstLaneRows6401, keyErrors6401, keyRedundancy6401,
    n6401, ownerDegreeCap6401, bchksErrors6401]
theorem fullTwoLaneSupportMatrix_rank_fork6401
    {F : Type*} [Field F]
    (alpha d₀ d₁ : Fin keyErrors6401 → F) :
    (fullTwoLaneSupportMatrix6401 alpha d₀ d₁).rank = keyErrors6401 ∨
      (fullTwoLaneSupportMatrix6401 alpha d₀ d₁).rank < keyErrors6401 := by
  have hle : (fullTwoLaneSupportMatrix6401 alpha d₀ d₁).rank ≤
      keyErrors6401 := by
    simpa only [Fintype.card_fin] using
      Matrix.rank_le_card_width
        (fullTwoLaneSupportMatrix6401 alpha d₀ d₁)
  omega
noncomputable def fullTwoLaneKeyMatrixZ6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F) :
    Matrix FullTwoLaneKeyRow6401 (Fin keyErrors6401) F[X] :=
  fun row col =>
    match row with
    | Sum.inl a => affineSyndromeZ alpha u₀ u₁ (a.1 + col.1)
    | Sum.inr a =>
        frobeniusSyndromeZ sigma q6401 alpha u₀ u₁ (a.1 + col.1)
theorem fullTwoLaneKeyMatrixZ_entry_degree6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F) :
    ∀ row col,
      (fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁ row col).natDegree ≤
        match row with
        | Sum.inl _ => 1
        | Sum.inr _ => q6401 := by
  intro row col
  cases row with
  | inl a => exact affineSyndromeZ_natDegree_le_one alpha u₀ u₁ _
  | inr a =>
      exact frobeniusSyndromeZ_natDegree_le (F := F) (ι := ι)
        sigma q6401 alpha u₀ u₁ _
theorem fullTwoLaneKeyMatrixZ_eval_entry6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (z : F) (hz : sigma z = z ^ q6401) :
    ∀ row col,
      Polynomial.eval z
          (fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁ row col) =
        match row with
        | Sum.inl a =>
            weightedSyndrome alpha (fun i => u₀ i + z * u₁ i)
              (a.1 + col.1)
        | Sum.inr a =>
            weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i))
              (a.1 + col.1) := by
  intro row col
  cases row with
  | inl a => exact affineSyndromeZ_eval alpha u₀ u₁ _ z
  | inr a =>
      simpa [fullTwoLaneKeyMatrixZ6401] using
        (frobeniusSyndromeZ_eval (F := F) (ι := ι)
          sigma q6401 alpha u₀ u₁ (a.1 + col.1) z hz)
def selectedFullTwoLaneRow6401
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    KeyMinorRow6401 → FullTwoLaneKeyRow6401
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (rho b)
noncomputable def twoLaneKeyMinorZ6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    Matrix KeyMinorRow6401 KeyMinorRow6401 F[X] :=
  fun row col =>
    match row with
    | Sum.inl a =>
        affineSyndromeZ alpha u₀ u₁
          (a.1 + (keyMinorColumnEquiv6401 col).1)
    | Sum.inr b =>
        frobeniusSyndromeZ sigma q6401 alpha u₀ u₁
          ((rho b).1 + (keyMinorColumnEquiv6401 col).1)
theorem twoLaneKeyMinorZ_eq_fullSubmatrix6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho =
      (fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).submatrix
        (selectedFullTwoLaneRow6401 rho) keyMinorColumnEquiv6401 := by
  ext row col
  cases row <;> rfl
noncomputable def twoLaneKeyRhsZ6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    KeyMinorRow6401 → F[X]
  | Sum.inl a =>
      -affineSyndromeZ alpha u₀ u₁ (a.1 + keyErrors6401)
  | Sum.inr b =>
      -frobeniusSyndromeZ sigma q6401 alpha u₀ u₁
        ((rho b).1 + keyErrors6401)
theorem twoLaneKeyRhsZ_degree6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    ∀ row,
      (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho row).natDegree ≤
        keyMinorRowCap6401 row := by
  intro row
  cases row with
  | inl a =>
      simpa [twoLaneKeyRhsZ6401, keyMinorRowCap6401] using
        (affineSyndromeZ_natDegree_le_one alpha u₀ u₁
          (a.1 + keyErrors6401))
  | inr b =>
      simpa [twoLaneKeyRhsZ6401, keyMinorRowCap6401] using
        (frobeniusSyndromeZ_natDegree_le (F := F) (ι := ι)
          sigma q6401 alpha u₀ u₁ ((rho b).1 + keyErrors6401))
theorem twoLaneKeyRhsZ_eval6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (z : F) (hz : sigma z = z ^ q6401) :
    ∀ row,
      Polynomial.eval z
          (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho row) =
        match row with
        | Sum.inl a =>
            -weightedSyndrome alpha (fun i => u₀ i + z * u₁ i)
              (a.1 + keyErrors6401)
        | Sum.inr b =>
            -weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i))
              ((rho b).1 + keyErrors6401) := by
  intro row
  cases row with
  | inl a =>
      simpa [twoLaneKeyRhsZ6401] using congrArg Neg.neg
        (affineSyndromeZ_eval alpha u₀ u₁
          (a.1 + keyErrors6401) z)
  | inr b =>
      simpa [twoLaneKeyRhsZ6401] using congrArg Neg.neg
        (frobeniusSyndromeZ_eval (F := F) (ι := ι)
          sigma q6401 alpha u₀ u₁
            ((rho b).1 + keyErrors6401) z hz)
theorem twoLaneKeyMinorZ_entry_degree6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    ∀ row col,
      (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho row col).natDegree ≤
        keyMinorRowCap6401 row := by
  intro row col
  cases row with
  | inl a =>
      exact affineSyndromeZ_natDegree_le_one alpha u₀ u₁ _
  | inr b =>
      exact frobeniusSyndromeZ_natDegree_le
        sigma q6401 alpha u₀ u₁ _
theorem twoLaneKeyMinorZ_det_degree6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401) :
    (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).det.natDegree ≤
      keyMinorDegreeCap6401 := by
  calc
    (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).det.natDegree ≤
        ∑ i, keyMinorRowCap6401 i :=
      natDegree_det_le_sum_rowCaps _ keyMinorRowCap6401
        (twoLaneKeyMinorZ_entry_degree6401 sigma alpha u₀ u₁ rho)
    _ = keyMinorDegreeCap6401 := keyMinorRowCap_sum_exact6401
theorem twoLaneKeyMinorZ_eval_entry6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (z : F) (hz : sigma z = z ^ q6401) :
    ∀ row col,
      Polynomial.eval z
          (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho row col) =
        match row with
        | Sum.inl a =>
            weightedSyndrome alpha (fun i => u₀ i + z * u₁ i)
              (a.1 + (keyMinorColumnEquiv6401 col).1)
        | Sum.inr b =>
            weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i))
              ((rho b).1 + (keyMinorColumnEquiv6401 col).1) := by
  intro row col
  cases row with
  | inl a => exact affineSyndromeZ_eval alpha u₀ u₁ _ z
  | inr b =>
      exact frobeniusSyndromeZ_eval (F := F) (ι := ι)
        sigma q6401 alpha u₀ u₁ _ z hz
theorem fixed_minor_nonzero_of_anchor6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (z₀ : F)
    (hanchor : Polynomial.eval z₀
      (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).det ≠ 0) :
    (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).det ≠ 0 := by
  intro hzero
  rw [hzero, Polynomial.eval_zero] at hanchor
  exact hanchor rfl
theorem twoLane_minor_natDegree_le6401
    {F : Type*} [Field F]
    (M : Matrix KeyMinorRow6401 KeyMinorRow6401 F[X])
    (hentry : ∀ i j, (M i j).natDegree ≤ keyMinorRowCap6401 i) :
    M.det.natDegree ≤ keyMinorDegreeCap6401 := by
  calc
    M.det.natDegree ≤ ∑ i, keyMinorRowCap6401 i :=
      natDegree_det_le_sum_rowCaps M keyMinorRowCap6401 hentry
    _ = keyMinorDegreeCap6401 := keyMinorRowCap_sum_exact6401
theorem twoLane_cramerNumerator_natDegree_le6401
    {F : Type*} [Field F]
    (M : Matrix KeyMinorRow6401 KeyMinorRow6401 F[X])
    (b : KeyMinorRow6401 → F[X]) (j₀ : KeyMinorRow6401)
    (hentry : ∀ i j, (M i j).natDegree ≤ keyMinorRowCap6401 i)
    (hb : ∀ i, (b i).natDegree ≤ keyMinorRowCap6401 i) :
    (M.updateCol j₀ b).det.natDegree ≤ keyMinorDegreeCap6401 := by
  apply twoLane_minor_natDegree_le6401
  intro i j
  by_cases h : j = j₀
  · subst j
    simpa using hb i
  · simpa [Matrix.updateCol, h] using hentry i j
noncomputable def cramerSolution
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (A : Matrix I I F) (b : I → F) : I → F :=
  (A.det)⁻¹ • A.cramer b
theorem cramerSolution_mulVec
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (A : Matrix I I F) (b : I → F) (hA : A.det ≠ 0) :
    A.mulVec (cramerSolution A b) = b := by
  rw [cramerSolution, Matrix.mulVec_smul, Matrix.mulVec_cramer]
  ext i
  simp [hA]
theorem cramerSolution_unique
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (A : Matrix I I F) (b x : I → F) (hA : A.det ≠ 0)
    (hx : A.mulVec x = b) :
    x = cramerSolution A b := by
  have hs := cramerSolution_mulVec A b hA
  have hz : A.mulVec (x - cramerSolution A b) = 0 := by
    rw [Matrix.mulVec_sub, hx, hs, sub_self]
  have hzv := Matrix.eq_zero_of_mulVec_eq_zero hA hz
  exact sub_eq_zero.mp hzv
theorem cramer_eq_det_smul_of_mulVec_eq
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (A : Matrix I I F) (b c : I → F) (hA : A.det ≠ 0)
    (hc : A.mulVec c = b) :
    A.cramer b = A.det • c := by
  have hz : A.mulVec (A.cramer b - A.det • c) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_cramer, Matrix.mulVec_smul,
      hc, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hA hz)
theorem eval_polynomialMatrix_det
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (z : F) :
    Polynomial.eval z M.det =
      (M.map (Polynomial.evalRingHom z)).det := by
  exact RingHom.map_det (Polynomial.evalRingHom z) M
theorem eval_polynomialMatrix_cramer
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (b : I → F[X]) (z : F) (j : I) :
    Polynomial.eval z (M.cramer b j) =
      (M.map (Polynomial.evalRingHom z)).cramer
        (fun i => Polynomial.eval z (b i)) j := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply]
  calc
    Polynomial.eval z (M.updateCol j b).det =
        ((M.updateCol j b).map (Polynomial.evalRingHom z)).det :=
      eval_polynomialMatrix_det (M.updateCol j b) z
    _ = ((M.map (Polynomial.evalRingHom z)).updateCol j
        fun i => Polynomial.eval z (b i)).det := by
      congr 1
      ext i k
      by_cases hk : k = j
      · subst k
        simp [Matrix.updateCol]
      · simp [Matrix.updateCol, hk]
noncomputable def clearedLocatorCoordinate
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (b : I → F[X]) (pow : I → Nat)
    (t : Nat) (x : F) : F[X] :=
  M.det * Polynomial.C (x ^ t) +
    ∑ j, M.cramer b j * Polynomial.C (x ^ pow j)
theorem clearedLocatorCoordinate_root
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (b : I → F[X]) (pow : I → Nat)
    (t : Nat) (x z : F) (c : I → F)
    (hdet : Polynomial.eval z M.det ≠ 0)
    (hsys : (M.map (Polynomial.evalRingHom z)).mulVec c =
      fun i => Polynomial.eval z (b i))
    (hroot : x ^ t + ∑ j, c j * x ^ pow j = 0) :
    Polynomial.eval z (clearedLocatorCoordinate M b pow t x) = 0 := by
  classical
  let Az := M.map (Polynomial.evalRingHom z)
  let bz : I → F := fun i => Polynomial.eval z (b i)
  have hdet' : Az.det ≠ 0 := by
    change (M.map (Polynomial.evalRingHom z)).det ≠ 0
    rw [← eval_polynomialMatrix_det M z]
    exact hdet
  have hcr := cramer_eq_det_smul_of_mulVec_eq Az bz c hdet' hsys
  simp only [clearedLocatorCoordinate, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finsetSum]
  rw [show Polynomial.eval z M.det = Az.det by
      exact eval_polynomialMatrix_det M z]
  simp_rw [eval_polynomialMatrix_cramer M b z]
  rw [hcr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j : I, Az.det * c j * x ^ pow j) =
      Az.det * (∑ j : I, c j * x ^ pow j) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  rw [← mul_add, hroot, mul_zero]
theorem clearedLocatorCoordinate_natDegree_le
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (b : I → F[X]) (pow : I → Nat)
    (t D : Nat) (x : F)
    (hdet : M.det.natDegree ≤ D)
    (hcr : ∀ j, (M.cramer b j).natDegree ≤ D) :
    (clearedLocatorCoordinate M b pow t x).natDegree ≤ D := by
  unfold clearedLocatorCoordinate
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (by simpa using hdet)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact Polynomial.natDegree_mul_le.trans (by simpa using hcr j)
theorem twoLaneKeyCramerNumerator_degree6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (j : KeyMinorRow6401) :
    ((twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).cramer
      (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho) j).natDegree ≤
        keyMinorDegreeCap6401 := by
  rw [Matrix.cramer_apply]
  exact twoLane_cramerNumerator_natDegree_le6401
    (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho)
    (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho) j
    (twoLaneKeyMinorZ_entry_degree6401 sigma alpha u₀ u₁ rho)
    (twoLaneKeyRhsZ_degree6401 sigma alpha u₀ u₁ rho)
noncomputable def twoLaneClearedLocatorCoordinate6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (x : F) : F[X] :=
  clearedLocatorCoordinate
    (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho)
    (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho)
    (fun j => (keyMinorColumnEquiv6401 j).1)
    keyErrors6401 x
theorem twoLaneClearedLocatorCoordinate_degree6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (x : F) :
    (twoLaneClearedLocatorCoordinate6401
      sigma alpha u₀ u₁ rho x).natDegree ≤ keyMinorDegreeCap6401 := by
  apply clearedLocatorCoordinate_natDegree_le
  · exact twoLaneKeyMinorZ_det_degree6401 sigma alpha u₀ u₁ rho
  · exact twoLaneKeyCramerNumerator_degree6401 sigma alpha u₀ u₁ rho
theorem twoLaneKey_coefficients_unique_at_challenge6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (z : F)
    (hdet : Polynomial.eval z
      (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).det ≠ 0)
    (c : KeyMinorRow6401 → F)
    (hsys :
      ((twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).map
          (Polynomial.evalRingHom z)).mulVec c =
        fun i => Polynomial.eval z
          (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho i)) :
    c = cramerSolution
      ((twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).map
        (Polynomial.evalRingHom z))
      (fun i => Polynomial.eval z
        (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho i)) := by
  apply cramerSolution_unique
  · rw [← eval_polynomialMatrix_det]
    exact hdet
  · exact hsys
theorem twoLaneClearedLocatorCoordinate_root6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha u₀ u₁ : ι → F)
    (rho : Fin keySecondLaneRows6401 → Fin keyFirstLaneRows6401)
    (x z : F) (c : KeyMinorRow6401 → F)
    (hdet : Polynomial.eval z
      (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).det ≠ 0)
    (hsys :
      ((twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho).map
          (Polynomial.evalRingHom z)).mulVec c =
        fun i => Polynomial.eval z
          (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho i))
    (hroot : x ^ keyErrors6401 +
      ∑ j : KeyMinorRow6401,
        c j * x ^ (keyMinorColumnEquiv6401 j).1 = 0) :
    Polynomial.eval z
      (twoLaneClearedLocatorCoordinate6401
        sigma alpha u₀ u₁ rho x) = 0 := by
  exact clearedLocatorCoordinate_root
    (twoLaneKeyMinorZ6401 sigma alpha u₀ u₁ rho)
    (twoLaneKeyRhsZ6401 sigma alpha u₀ u₁ rho)
    (fun j => (keyMinorColumnEquiv6401 j).1)
    keyErrors6401 x z c hdet hsys hroot
noncomputable def fixedLocatorCoordinates
    {F ι : Type} [Field F] [Fintype ι]
    (L : ι → F[X]) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => L i = 0
theorem locator_root_incidence
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (S : Finset F) (A : F → Finset ι) (L : ι → F[X])
    (t D : Nat)
    (hcard : ∀ z ∈ S, t ≤ (A z).card)
    (hroot : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval z (L i) = 0)
    (hdegree : ∀ i, (L i).natDegree ≤ D) :
    S.card * (t - (fixedLocatorCoordinates L).card) ≤
      (Fintype.card ι - (fixedLocatorCoordinates L).card) * D := by
  classical
  let H : Finset ι := fixedLocatorCoordinates L
  let E : F → Finset ι := fun z => A z \ H
  let fib : ι → Nat := fun i => (S.filter fun z => i ∈ E z).card
  have hrow : ∀ z ∈ S, t - H.card ≤ (E z).card := by
    intro z hz
    have hdiff := Finset.le_card_sdiff H (A z)
    exact (Nat.sub_le_sub_right (hcard z hz) H.card).trans hdiff
  have hlower : S.card * (t - H.card) ≤
      ∑ z ∈ S, (E z).card := by
    calc
      S.card * (t - H.card) = ∑ _z ∈ S, (t - H.card) := by simp
      _ ≤ ∑ z ∈ S, (E z).card := Finset.sum_le_sum hrow
  have hswap : (∑ z ∈ S, (E z).card) = ∑ i : ι, fib i := by
    exact sum_card_eq_sum_fiber_card S E
  have hfib : ∀ i ∉ H, fib i ≤ D := by
    intro i hi
    have hsub : S.filter (fun z => i ∈ E z) ⊆
        S.filter fun z => Polynomial.eval z (L i) = 0 := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hroot z hz.1 i (Finset.mem_sdiff.mp hz.2).1⟩
    have hLi : L i ≠ 0 := by
      intro hzero
      apply hi
      simp [H, fixedLocatorCoordinates, hzero]
    calc
      fib i ≤ (S.filter fun z => Polynomial.eval z (L i) = 0).card :=
        Finset.card_le_card hsub
      _ ≤ (L i).natDegree :=
        BCHKSTwoFrobeniusRankTwoSpecialization6401.card_filter_eval_eq_zero_le_natDegree
          S (L i) hLi
      _ ≤ D := hdegree i
  have hrestrict : (∑ i : ι, fib i) =
      ∑ i ∈ (Finset.univ \ H), fib i := by
    symm
    apply Finset.sum_subset
    · simp
    · intro i hi hnot
      have hiH : i ∈ H := by simpa using hnot
      simp [fib, E, hiH]
  calc
    S.card * (t - (fixedLocatorCoordinates L).card) =
        S.card * (t - H.card) := by rfl
    _ ≤ ∑ z ∈ S, (E z).card := hlower
    _ = ∑ i : ι, fib i := hswap
    _ = ∑ i ∈ (Finset.univ \ H), fib i := hrestrict
    _ ≤ ∑ _i ∈ (Finset.univ \ H), D := by
      apply Finset.sum_le_sum
      intro i hi
      exact hfib i (Finset.mem_sdiff.mp hi).2
    _ = (Fintype.card ι - H.card) * D := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_sdiff]
      simp
    _ = (Fintype.card ι -
        (fixedLocatorCoordinates L).card) * D := by rfl
theorem variableErrors_le_32_of_rootIncidence6401
    (c : Nat)
    (hinc : c * keyGoodChallengeFloor6401 ≤
      (bchksAgreements6401 + c) * keyMinorDegreeCap6401) :
    c ≤ keyVariableErrorCap6401 := by
  by_contra h
  have hc : 33 ≤ c := by
    norm_num [keyVariableErrorCap6401] at h ⊢
    omega
  have hstrict :
      (bchksAgreements6401 + c) * keyMinorDegreeCap6401 <
        c * keyGoodChallengeFloor6401 := by
    have hgap : keyMinorDegreeCap6401 < keyGoodChallengeFloor6401 := by
      norm_num [keyMinorDegreeCap6401, keyGoodChallengeFloor6401,
        weakCurveSeedInput6401, BCHKSFinalConditional6401.mcaNumerator6401,
        BCHKSList6401.maxMCANumeratorAfterList6401,
        BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
        BCHKSList6401.listBound6401, n6401, wideListBound, q6401,
        keyFirstLaneRows6401, keySecondLaneRows6401, keyRedundancy6401,
        keyErrors6401, ownerDegreeCap6401, bchksErrors6401]
    have hbase :
        (bchksAgreements6401 + 33) * keyMinorDegreeCap6401 <
          33 * keyGoodChallengeFloor6401 := by
      norm_num [bchksAgreements6401, keyMinorDegreeCap6401,
        keyGoodChallengeFloor6401, weakCurveSeedInput6401,
        BCHKSFinalConditional6401.mcaNumerator6401,
        BCHKSList6401.maxMCANumeratorAfterList6401,
        BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
        BCHKSList6401.listBound6401, n6401, wideListBound, q6401,
        keyFirstLaneRows6401, keySecondLaneRows6401, keyRedundancy6401,
        keyErrors6401, ownerDegreeCap6401, bchksErrors6401]
    have hc_decomp : bchksAgreements6401 + c =
        (bchksAgreements6401 + 33) + (c - 33) := by omega
    have hc_decomp' : c = 33 + (c - 33) := by omega
    calc
      (bchksAgreements6401 + c) * keyMinorDegreeCap6401 =
          (bchksAgreements6401 + 33) * keyMinorDegreeCap6401 +
            (c - 33) * keyMinorDegreeCap6401 := by
        rw [hc_decomp, Nat.add_mul]
      _ < 33 * keyGoodChallengeFloor6401 +
            (c - 33) * keyMinorDegreeCap6401 :=
        Nat.add_lt_add_right hbase _
      _ ≤ 33 * keyGoodChallengeFloor6401 +
            (c - 33) * keyGoodChallengeFloor6401 := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left (c - 33) hgap.le) _
      _ = c * keyGoodChallengeFloor6401 := by
        rw [← Nat.add_mul]
        exact congrArg (fun x => x * keyGoodChallengeFloor6401)
          hc_decomp'.symm
  exact (Nat.not_lt_of_ge hinc) hstrict
def genericRankMinorDegreeCap6401 (rho : Nat) : Nat :=
  min keyFirstLaneRows6401 rho +
    (rho - keyFirstLaneRows6401) * q6401
def genericRankVariableRootCap6401 (rho : Nat) : Nat :=
  ((n6401 - rho) * genericRankMinorDegreeCap6401 rho) /
    (weakCurveSeedInput6401 -
      2 * genericRankMinorDegreeCap6401 rho)
theorem genericRank_incidenceDenominator_pos_scan6401 :
    ∀ rho : Fin (keyErrors6401 + 1),
      0 < weakCurveSeedInput6401 -
        2 * genericRankMinorDegreeCap6401 rho.1 := by
  native_decide
theorem genericRank_variableRootCap_scan6401 :
    ∀ rho : Fin (keyErrors6401 + 1),
      genericRankVariableRootCap6401 rho.1 ≤
        keyVariableErrorCap6401 := by
  native_decide
theorem incidence_rearrange_without_c_on_rhs
    (c N D a : Nat) (h2 : 2 * D ≤ N)
    (h : c * (N - D) ≤ (a + c) * D) :
    c * (N - 2 * D) ≤ a * D := by
  have hD : D ≤ N := by omega
  have hbig : c * (N - 2 * D) + 2 * c * D ≤
      a * D + 2 * c * D := by
    calc
      c * (N - 2 * D) + 2 * c * D = c * N := by
        rw [show 2 * c * D = c * (2 * D) by ring,
          ← Nat.mul_add, Nat.sub_add_cancel h2]
      _ = c * (N - D) + c * D := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hD]
      _ ≤ (a + c) * D + c * D := Nat.add_le_add_right h _
      _ = a * D + 2 * c * D := by ring
  exact Nat.le_of_add_le_add_right hbig
theorem variableErrors_le_32_of_genericRankIncidence6401
    (rho c : Nat) (hrho : rho ≤ keyErrors6401)
    (hinc : c *
        (weakCurveSeedInput6401 - genericRankMinorDegreeCap6401 rho) ≤
      (n6401 - rho + c) * genericRankMinorDegreeCap6401 rho) :
    c ≤ keyVariableErrorCap6401 := by
  let r : Fin (keyErrors6401 + 1) :=
    ⟨rho, Nat.lt_succ_iff.mpr hrho⟩
  have hpos : 0 < weakCurveSeedInput6401 -
      2 * genericRankMinorDegreeCap6401 rho := by
    simpa [r] using genericRank_incidenceDenominator_pos_scan6401 r
  have hrearranged : c *
        (weakCurveSeedInput6401 -
          2 * genericRankMinorDegreeCap6401 rho) ≤
      (n6401 - rho) * genericRankMinorDegreeCap6401 rho :=
    incidence_rearrange_without_c_on_rhs c weakCurveSeedInput6401
      (genericRankMinorDegreeCap6401 rho) (n6401 - rho)
      (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hpos)) hinc
  have hquot : c ≤ genericRankVariableRootCap6401 rho := by
    exact (Nat.le_div_iff_mul_le hpos).2 hrearranged
  exact hquot.trans (by
    simpa [r] using genericRank_variableRootCap_scan6401 r)
theorem genericRank_commonCore_floor6401
    (rho c : Nat) (hrho : rho ≤ keyErrors6401)
    (hc : c ≤ keyVariableErrorCap6401) :
    147530 ≤ n6401 - (rho + (weakCurveOutput6401 - 1) * c) ∧
      ownerDegreeCap6401 + 1 ≤
        n6401 - (rho + (weakCurveOutput6401 - 1) * c) := by
  norm_num [keyErrors6401, keyVariableErrorCap6401,
    weakCurveOutput6401, targetSeedOutput, n6401, ownerDegreeCap6401,
    bchksErrors6401] at hrho hc ⊢
  omega
theorem errorSupport_union_card_le
    {ι ζ : Type} [DecidableEq ι] [DecidableEq ζ]
    (S : Finset ζ) (E : ζ → Finset ι) (H : Finset ι)
    (rho c : Nat) (hS : S.Nonempty)
    (hH : ∀ z ∈ S, H ⊆ E z)
    (hcard : ∀ z ∈ S, (E z).card = rho)
    (hvar : rho - H.card ≤ c) :
    (S.biUnion E).card ≤ rho + (S.card - 1) * c := by
  classical
  let V : ζ → Finset ι := fun z => E z \ H
  have hsub : S.biUnion E ⊆ H ∪ S.biUnion V := by
    intro i hi
    obtain ⟨z, hzS, hiE⟩ := Finset.mem_biUnion.mp hi
    by_cases hiH : i ∈ H
    · exact Finset.mem_union_left _ hiH
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨z, hzS, Finset.mem_sdiff.mpr ⟨hiE, hiH⟩⟩)
  have hVcard : ∀ z ∈ S, (V z).card = rho - H.card := by
    intro z hz
    rw [Finset.card_sdiff_of_subset (hH z hz), hcard z hz]
  have hVU : (S.biUnion V).card ≤ S.card * (rho - H.card) :=
    Finset.card_biUnion_le_card_mul S V (rho - H.card)
      (fun z hz => (hVcard z hz).le)
  have hHrho : H.card ≤ rho := by
    obtain ⟨z, hz⟩ := hS
    rw [← hcard z hz]
    exact Finset.card_le_card (hH z hz)
  calc
    (S.biUnion E).card ≤ (H ∪ S.biUnion V).card :=
      Finset.card_le_card hsub
    _ ≤ H.card + (S.biUnion V).card :=
      Finset.card_union_le H (S.biUnion V)
    _ ≤ H.card + S.card * (rho - H.card) :=
      Nat.add_le_add_left hVU _
    _ = rho + (S.card - 1) * (rho - H.card) := by
      have hScard : S.card = (S.card - 1) + 1 := by
        have := hS.card_pos
        omega
      rw [hScard]
      have hsplit : H.card + (rho - H.card) = rho :=
        Nat.add_sub_of_le hHrho
      calc
        H.card + ((S.card - 1) + 1) * (rho - H.card) =
            (H.card + (rho - H.card)) +
              (S.card - 1) * (rho - H.card) := by ring
        _ = rho + (S.card - 1) * (rho - H.card) := by rw [hsplit]
    _ ≤ rho + (S.card - 1) * c := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hvar) _
theorem keyEquation_commonCore_ledger6401 :
    keyErrors6401 +
        (weakCurveOutput6401 - 1) * keyVariableErrorCap6401 = 114614 ∧
      n6401 -
          (keyErrors6401 +
            (weakCurveOutput6401 - 1) * keyVariableErrorCap6401) = 147530 ∧
      ownerDegreeCap6401 + 1 = 131072 ∧
      131072 ≤ 147530 ∧
      147530 - 131072 = 16458 := by
  norm_num [keyErrors6401, keyVariableErrorCap6401,
    weakCurveOutput6401, targetSeedOutput, n6401, ownerDegreeCap6401,
    bchksErrors6401]
def TwoLaneFailureRelation
    {F ι : Type*} [Field F]
    (sigma : F →+* F) (alpha : ι → F) (E : ι → F)
    (W₀ W₁ : Polynomial F) : Prop :=
  ∀ i, W₀.eval (alpha i) * sigma (E i) =
    W₁.eval (alpha i) * E i
noncomputable def failurePrimitiveRow
    {F : Type*} [Field F]
    (P sigmaP W₀ W₁ : Polynomial F) : Fin 3 → Polynomial F := ![
  W₁ * P - W₀ * sigmaP,
  -W₁,
  W₀]
theorem failurePrimitiveRow_coordinateRelation6401
    {F ι : Type*} [Field F]
    (sigma : F →+* F) (alpha : ι → F)
    (u E : ι → F) (P sigmaP W₀ W₁ : Polynomial F)
    (hu : ∀ i, u i = P.eval (alpha i) + E i)
    (hsigmaP : ∀ i, sigma (P.eval (alpha i)) = sigmaP.eval (alpha i))
    (hfailure : TwoLaneFailureRelation sigma alpha E W₀ W₁) :
    ∀ i,
      (failurePrimitiveRow P sigmaP W₀ W₁ 0).eval (alpha i) +
        (failurePrimitiveRow P sigmaP W₀ W₁ 1).eval (alpha i) * u i +
        (failurePrimitiveRow P sigmaP W₀ W₁ 2).eval (alpha i) *
          sigma (u i) = 0 := by
  intro i
  have hsigmau : sigma (u i) =
      sigmaP.eval (alpha i) + sigma (E i) := by
    rw [hu i, map_add, hsigmaP i]
  have hf := hfailure i
  change (W₁ * P - W₀ * sigmaP).eval (alpha i) +
      (-W₁).eval (alpha i) * u i + W₀.eval (alpha i) * sigma (u i) = 0
  rw [hsigmau, hu i]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg]
  linear_combination hf
theorem failurePrimitiveRow_degreeCaps6401
    {F : Type*} [Field F]
    (P sigmaP W₀ W₁ : Polynomial F)
    (hP : P.natDegree ≤ ownerDegreeCap6401)
    (hsigmaP : sigmaP.natDegree ≤ ownerDegreeCap6401)
    (hW₀ : W₀.natDegree ≤ keySecondLaneRows6401 - 1)
    (hW₁ : W₁.natDegree ≤ keySecondLaneRows6401 - 1) :
    (failurePrimitiveRow P sigmaP W₀ W₁ 0).natDegree ≤ 153578 ∧
      (failurePrimitiveRow P sigmaP W₀ W₁ 1).natDegree ≤ 22507 ∧
      (failurePrimitiveRow P sigmaP W₀ W₁ 2).natDegree ≤ 22507 := by
  have h0 : (W₁ * P - W₀ * sigmaP).natDegree ≤ 153578 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans <|
        (Nat.add_le_add hW₁ hP).trans (by
          norm_num [keySecondLaneRows6401, keyFirstLaneRows6401,
            keyRedundancy6401, keyErrors6401, n6401,
            ownerDegreeCap6401, bchksErrors6401])
    · exact Polynomial.natDegree_mul_le.trans <|
        (Nat.add_le_add hW₀ hsigmaP).trans (by
          norm_num [keySecondLaneRows6401, keyFirstLaneRows6401,
            keyRedundancy6401, keyErrors6401, n6401,
            ownerDegreeCap6401, bchksErrors6401])
  constructor
  · simpa [failurePrimitiveRow] using h0
  constructor
  · simpa [failurePrimitiveRow, keySecondLaneRows6401,
      keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      n6401, ownerDegreeCap6401, bchksErrors6401] using hW₁
  · simpa [failurePrimitiveRow, keySecondLaneRows6401,
      keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      n6401, ownerDegreeCap6401, bchksErrors6401] using hW₀
end BCHKSFrobeniusKeyEquationFork6401
end ProximityPrize.SubmissionLower

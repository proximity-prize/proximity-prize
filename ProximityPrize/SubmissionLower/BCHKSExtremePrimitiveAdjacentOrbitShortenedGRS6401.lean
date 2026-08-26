import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAdjacentOrbitShortenedGRS6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
section FiniteGRSConverse
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
noncomputable def finiteSupportCoweight6401
    (alpha : I ↪ F) (i : I) : F :=
  ∏ j ∈ (Finset.univ : Finset I).erase i, (alpha i - alpha j)
theorem finiteSupportCoweight_ne_zero6401
    (alpha : I ↪ F) (i : I) : finiteSupportCoweight6401 alpha i ≠ 0 := by
  unfold finiteSupportCoweight6401
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr (alpha.injective.ne hji.symm)
theorem syndromeWeight_mul_finiteSupportCoweight6401
    (alpha : I ↪ F) (i : I) :
    syndromeWeight alpha i * finiteSupportCoweight6401 alpha i = 1 := by
  have hco := finiteSupportCoweight_ne_zero6401 alpha i
  unfold syndromeWeight Lagrange.nodalWeight finiteSupportCoweight6401
  rw [Finset.prod_inv_distrib]
  exact inv_mul_cancel₀ hco
noncomputable def finiteSupportDualPolynomial6401
    (alpha : I ↪ F) (x : I → F) : F[X] :=
  Lagrange.interpolate Finset.univ alpha
    (fun i ↦ x i * finiteSupportCoweight6401 alpha i)
theorem finiteSupportDualPolynomial_eval6401
    (alpha : I ↪ F) (x : I → F) (i : I) :
    (finiteSupportDualPolynomial6401 alpha x).eval (alpha i) =
      x i * finiteSupportCoweight6401 alpha i := by
  unfold finiteSupportDualPolynomial6401
  exact Lagrange.eval_interpolate_at_node _ alpha.injective.injOn
    (Finset.mem_univ i)
theorem finiteSupportDualPolynomial_natDegree_lt6401
    (alpha : I ↪ F) (x : I → F) (rows : Nat)
    (hrows : rows < Fintype.card I)
    (hmoments : ∀ r : Fin rows,
      ∑ i, x i * alpha i ^ r.1 = 0) :
    (finiteSupportDualPolynomial6401 alpha x).natDegree <
      Fintype.card I - rows := by
  classical
  let W := finiteSupportDualPolynomial6401 alpha x
  let e := Fintype.card I
  have hWdegree : W.degree < (e : WithBot Nat) := by
    simpa [W, e, finiteSupportDualPolynomial6401] using
      (Lagrange.degree_interpolate_lt
        (s := (Finset.univ : Finset I))
        (r := fun i ↦ x i * finiteSupportCoweight6401 alpha i)
        alpha.injective.injOn)
  by_cases hWzero : W = 0
  · simp [W, hWzero, e, Nat.sub_pos_of_lt hrows]
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
  let Q : F[X] := W * Polynomial.X ^ j
  have hXpow : (Polynomial.X : F[X]) ^ j ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hQzero : Q ≠ 0 := mul_ne_zero hWzero hXpow
  have hjadd : W.natDegree + j = e - 1 := by
    dsimp [j]
    omega
  have hQnat : Q.natDegree < e := by
    rw [show Q.natDegree = W.natDegree + j by
      calc
        Q.natDegree = W.natDegree +
            ((Polynomial.X : F[X]) ^ j).natDegree := by
          exact Polynomial.natDegree_mul hWzero hXpow
        _ = W.natDegree + j := by simp]
    omega
  have hQdegree : Q.degree < (e : WithBot Nat) :=
    (Polynomial.natDegree_lt_iff_degree_lt hQzero).1 hQnat
  have hc := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset I)) (v := fun i ↦ alpha i)
    alpha.injective.injOn (by simpa [e] using hQdegree)
  have hc0 : Q.coeff (e - 1) = 0 := by
    rw [show Q.coeff (e - 1) =
        ∑ i : I, Q.eval (alpha i) /
          ∏ k ∈ (Finset.univ : Finset I).erase i,
            (alpha i - alpha k) by simpa [e] using hc]
    calc
      (∑ i : I, Q.eval (alpha i) /
          ∏ k ∈ (Finset.univ : Finset I).erase i,
            (alpha i - alpha k)) =
          ∑ i : I, x i * alpha i ^ j := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hco := finiteSupportCoweight_ne_zero6401 alpha i
        have hWeval : W.eval (alpha i) =
            x i * finiteSupportCoweight6401 alpha i := by
          simpa [W] using finiteSupportDualPolynomial_eval6401 alpha x i
        rw [show Q.eval (alpha i) =
            (x i * finiteSupportCoweight6401 alpha i) * alpha i ^ j by
          simp only [Q, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, hWeval]]
        unfold finiteSupportCoweight6401 at hco ⊢
        field_simp
      _ = 0 := hsum
  have hcoeffne : Q.coeff (e - 1) ≠ 0 := by
    dsimp [Q]
    rw [← hjadd, Polynomial.coeff_mul_X_pow,
      Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hWzero
  exact hcoeffne hc0
theorem exists_polynomial_of_weightedSyndromes_zero_finite_rows6401
    (alpha : I ↪ F) (y : I → F) (rows : Nat)
    (hrows : rows < Fintype.card I)
    (hzero : ∀ j : Fin rows, weightedSyndrome alpha y j.1 = 0) :
    ∃ Q : F[X], Q.natDegree < Fintype.card I - rows ∧
      ∀ i, Q.eval (alpha i) = y i := by
  classical
  let x : I → F := fun i ↦ syndromeWeight alpha i * y i
  let Q := finiteSupportDualPolynomial6401 alpha x
  have hmoments : ∀ j : Fin rows,
      ∑ i, x i * alpha i ^ j.1 = 0 := by
    intro j
    simpa [x, weightedSyndrome, mul_assoc, mul_left_comm, mul_comm] using
      hzero j
  have hQlt : Q.natDegree < Fintype.card I - rows :=
    finiteSupportDualPolynomial_natDegree_lt6401 alpha x rows hrows hmoments
  refine ⟨Q, hQlt, ?_⟩
  intro i
  have heval := finiteSupportDualPolynomial_eval6401 alpha x i
  change Q.eval (alpha i) = y i
  rw [show Q.eval (alpha i) =
      x i * finiteSupportCoweight6401 alpha i by simpa [Q] using heval]
  dsimp [x]
  calc
    syndromeWeight alpha i * y i * finiteSupportCoweight6401 alpha i =
        (syndromeWeight alpha i * finiteSupportCoweight6401 alpha i) *
          y i := by ring
    _ = 1 * y i := by
      rw [syndromeWeight_mul_finiteSupportCoweight6401 alpha i]
    _ = y i := one_mul _
end FiniteGRSConverse
section BenchmarkWindow
def adjacentOrbitShortenedTargetDegree6401 : Nat :=
  homogeneousDirectionCap6401 + ownerDegreeCap6401
noncomputable def adjacentOrbitShortenedRows6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {Owner : F → F[X]}
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) : Nat :=
  Fintype.card (TwoRowGoodIndex6401 W) -
    (adjacentOrbitShortenedTargetDegree6401 + 1)
theorem adjacentOrbitShortened_parameters_exact6401 :
    adjacentOrbitShortenedTargetDegree6401 = 153578 ∧
      n6401 - homogeneousDirectionCap6401 = 239637 ∧
      239637 - (adjacentOrbitShortenedTargetDegree6401 + 1) = 86058 := by
  native_decide
theorem twoRowGoodIndex_card_eq6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {Owner : F → F[X]}
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    Fintype.card (TwoRowGoodIndex6401 W) =
      n6401 - (twoRowSourceBadCoordinates6401 W).card := by
  classical
  change Fintype.card
      {i : Fin n6401 // ¬ i ∈ twoRowSourceBadCoordinates6401 W} = _
  rw [Fintype.card_subtype_compl]
  change Fintype.card (Fin n6401) -
      Fintype.card ↥(twoRowSourceBadCoordinates6401 W) = _
  rw [Fintype.card_fin, Fintype.card_coe]
theorem adjacentOrbitShortened_window_ledger6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {Owner : F → F[X]}
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (hbad : (twoRowSourceBadCoordinates6401 W).card ≤
      homogeneousDirectionCap6401) :
    239637 ≤ Fintype.card (TwoRowGoodIndex6401 W) ∧
      86058 ≤ adjacentOrbitShortenedRows6401 W ∧
      adjacentOrbitShortenedRows6401 W <
        Fintype.card (TwoRowGoodIndex6401 W) ∧
      Fintype.card (TwoRowGoodIndex6401 W) -
          adjacentOrbitShortenedRows6401 W = 153579 := by
  have hcard := twoRowGoodIndex_card_eq6401 W
  have htarget := adjacentOrbitShortened_parameters_exact6401
  simp only [adjacentOrbitShortenedRows6401]
  norm_num [n6401, homogeneousDirectionCap6401] at hbad hcard
  norm_num [adjacentOrbitShortenedTargetDegree6401,
    homogeneousDirectionCap6401, ownerDegreeCap6401] at htarget ⊢
  omega
end BenchmarkWindow
section SourceReconstruction
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem exists_adjacentOrbitShortenedDirectionPolynomial6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hadjacent : A = B.map sigma)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hBdegree : B.natDegree ≤ homogeneousDirectionCap6401)
    (hOwnerDegree : ∀ z ∈ S,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (T : Finset F) (hT : T ⊆ R.goodChallenges6401)
    (hTS : T ⊆ S)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hlarge : q6401 < T.card) :
    ∃ Q1 : F[X],
      Q1.natDegree ≤ adjacentOrbitShortenedTargetDegree6401 ∧
      ∀ i : TwoRowGoodIndex6401 W,
        Q1.eval (twoRowGoodAlpha6401 W i) =
          adjacentOrbitShortenedReceivedDirection6401 W B i := by
  have hbad := twoRowSourceBadCoordinates_card_le_22507_of_terminalLanes6401
    W R G A B hG hA hB hzero hone
  have hledger := adjacentOrbitShortened_window_ledger6401 W (by
    simpa [homogeneousDirectionCap6401] using hbad)
  let rows := adjacentOrbitShortenedRows6401 W
  have hrows : rows < Fintype.card (TwoRowGoodIndex6401 W) := by
    simpa [rows] using hledger.2.2.1
  have hproductDegree : ∀ z ∈ T,
      (B * Owner z).natDegree ≤
        adjacentOrbitShortenedTargetDegree6401 := by
    intro z hz
    calc
      (B * Owner z).natDegree ≤ B.natDegree + (Owner z).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ homogeneousDirectionCap6401 + ownerDegreeCap6401 :=
        Nat.add_le_add hBdegree (hOwnerDegree z (hTS hz))
      _ = adjacentOrbitShortenedTargetDegree6401 := rfl
  have hzeroSyndromes : ∀ j : Fin rows,
      weightedSyndrome (twoRowGoodAlpha6401 W)
        (adjacentOrbitShortenedReceivedDirection6401 W B) j.1 = 0 := by
    intro j
    apply adjacentOrbit_manyOwners_shortenedDirectionSyndrome_zero6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
        hfixedCard T hT hTG hlarge j.1
    intro z hz
    have hj := j.2
    have hdeg := hproductDegree z hz
    have htarget := adjacentOrbitShortened_parameters_exact6401.1
    have hcard := hledger.1
    dsimp [rows, adjacentOrbitShortenedRows6401] at hj
    omega
  obtain ⟨Q1, hQdegree, hQeval⟩ :=
    exists_polynomial_of_weightedSyndromes_zero_finite_rows6401
      (twoRowGoodAlpha6401 W)
      (adjacentOrbitShortenedReceivedDirection6401 W B)
      rows hrows hzeroSyndromes
  refine ⟨Q1, ?_, hQeval⟩
  have hcodim := hledger.2.2.2
  rw [show Fintype.card (TwoRowGoodIndex6401 W) - rows = 153579 by
    simpa [rows] using hcodim] at hQdegree
  have htarget := adjacentOrbitShortened_parameters_exact6401.1
  rw [htarget]
  omega
theorem punctureLocator_mul_shortenedDirection_fullDomain6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (B Q1 : F[X])
    (hQeval : ∀ i : TwoRowGoodIndex6401 W,
      Q1.eval (twoRowGoodAlpha6401 W i) =
        adjacentOrbitShortenedReceivedDirection6401 W B i) :
    ∀ i : Fin n6401,
      (twoRowSourcePunctureLocator6401 W * Q1).eval (alpha i) =
        (twoRowSourcePunctureLocator6401 W * B).eval (alpha i) * u1 i := by
  intro i
  simp only [Polynomial.eval_mul]
  by_cases hi : i ∈ twoRowSourceBadCoordinates6401 W
  · rw [twoRowSourcePunctureLocator_eval_eq_zero6401 W i hi]
    simp
  · have hQi := hQeval ⟨i, hi⟩
    simp only [twoRowGoodAlpha6401,
      adjacentOrbitShortenedReceivedDirection6401] at hQi
    change Q1.eval (alpha i) = B.eval (alpha i) * u1 i at hQi
    rw [hQi]
    ring
theorem punctureLocator_mul_shortenedDirection_natDegree_le_176085_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (Q1 : F[X])
    (hbad : (twoRowSourceBadCoordinates6401 W).card ≤
      homogeneousDirectionCap6401)
    (hQdegree : Q1.natDegree ≤
      adjacentOrbitShortenedTargetDegree6401) :
    (twoRowSourcePunctureLocator6401 W * Q1).natDegree ≤ 176085 := by
  calc
    (twoRowSourcePunctureLocator6401 W * Q1).natDegree ≤
        (twoRowSourcePunctureLocator6401 W).natDegree + Q1.natDegree :=
      Polynomial.natDegree_mul_le
    _ = (twoRowSourceBadCoordinates6401 W).card + Q1.natDegree := by
      rw [twoRowSourcePunctureLocator_natDegree6401]
    _ ≤ homogeneousDirectionCap6401 +
        adjacentOrbitShortenedTargetDegree6401 :=
      Nat.add_le_add hbad hQdegree
    _ = 176085 := by native_decide
end SourceReconstruction
end BCHKSExtremePrimitiveAdjacentOrbitShortenedGRS6401
end ProximityPrize.SubmissionLower

import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalFixedPairPackage6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusConstantPairEndpoint6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusConstantPairEndpoint6401
open BCHKSSubfieldFrobenius6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFixedLaneRecurrence6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveTerminalFixedPairPackage6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section PointwiseAdjacentOrbit
variable {F : Type*} [Field F]
theorem coprimePolynomial_evals_not_both_zero6401
    (A B : F[X]) (hcoprime : IsCoprime A B) (x : F) :
    A.eval x ≠ 0 ∨ B.eval x ≠ 0 := by
  by_contra hzero
  rw [not_or] at hzero
  have hAzero : A.eval x = 0 := not_ne_iff.mp hzero.1
  have hBzero : B.eval x = 0 := not_ne_iff.mp hzero.2
  obtain ⟨U, V, hbezout⟩ := hcoprime
  have heval := congrArg (Polynomial.eval x) hbezout
  simp [hAzero, hBzero] at heval
theorem adjacentOrbit_rightEval_ne_zero6401
    (sigma : F →+* F) (x : F) (A B : F[X])
    (hfixed : sigma x = x) (hadjacent : A = B.map sigma)
    (hnotBoth : A.eval x ≠ 0 ∨ B.eval x ≠ 0) :
    B.eval x ≠ 0 := by
  intro hBzero
  rcases hnotBoth with hAne | hBne
  · apply hAne
    rw [hadjacent,
      eval_map_eq_map_eval_of_fixed sigma B x hfixed,
      hBzero, map_zero]
  · exact hBne hBzero
theorem adjacentOrbit_rightEval_ne_zero_of_isCoprime6401
    (sigma : F →+* F) (x : F) (A B : F[X])
    (hfixed : sigma x = x) (hadjacent : A = B.map sigma)
    (hcoprime : IsCoprime A B) :
    B.eval x ≠ 0 :=
  adjacentOrbit_rightEval_ne_zero6401 sigma x A B hfixed hadjacent
    (coprimePolynomial_evals_not_both_zero6401 A B hcoprime x)
theorem adjacentOrbit_weightedError_fixed6401
    (sigma : F →+* F) (x e : F) (A B : F[X])
    (hfixed : sigma x = x) (hadjacent : A = B.map sigma)
    (hrelation : A.eval x * sigma e = B.eval x * e) :
    sigma (B.eval x * e) = B.eval x * e := by
  rw [map_mul]
  have hAeval : A.eval x = sigma (B.eval x) := by
    rw [hadjacent, eval_map_eq_map_eval_of_fixed sigma B x hfixed]
  rw [← hAeval]
  exact hrelation
theorem adjacentOrbit_weightedError_fixed_and_nonzero_iff6401
    (sigma : F →+* F) (x e : F) (A B : F[X])
    (hfixed : sigma x = x) (hadjacent : A = B.map sigma)
    (hcoprime : IsCoprime A B)
    (hrelation : A.eval x * sigma e = B.eval x * e) :
    sigma (B.eval x * e) = B.eval x * e ∧
      (B.eval x * e ≠ 0 ↔ e ≠ 0) := by
  have hBne := adjacentOrbit_rightEval_ne_zero_of_isCoprime6401
    sigma x A B hfixed hadjacent hcoprime
  refine ⟨adjacentOrbit_weightedError_fixed6401
      sigma x e A B hfixed hadjacent hrelation, ?_⟩
  constructor
  · intro hproduct hezero
    exact hproduct (by rw [hezero, mul_zero])
  · exact fun he ↦ mul_ne_zero hBne he
end PointwiseAdjacentOrbit
section TwoRowTerminalLift
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
noncomputable def adjacentOrbitWeightedFullError6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (B : F[X]) (z : F) : Fin n6401 → F :=
  fun i ↦ B.eval (alpha i) * fullOwnerError6401 W z i
theorem twoRowSourcePunctureLocator_eval_ne_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (i : Fin n6401) (hi : i ∉ twoRowSourceBadCoordinates6401 W) :
    (twoRowSourcePunctureLocator6401 W).eval (alpha i) ≠ 0 := by
  classical
  simp only [twoRowSourcePunctureLocator6401, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  apply hi
  have hindex : i = j := alpha.injective hij
  simpa [hindex] using hj
theorem twoRowSourceBadCoordinates_card_le_22507_of_terminalLanes6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C) :
    (twoRowSourceBadCoordinates6401 W).card ≤ 22507 := by
  have hcaps :=
    twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G A B hG hA hB hzero hone
  have hlocator := twoRowSourcePunctureLocator_ne_zero6401 W
  have hdiv : twoRowSourcePunctureLocator6401 W ∣
      twoRowSourcePunctureLocator6401 W * A := ⟨A, rfl⟩
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv
    (mul_ne_zero hlocator hA)
  rw [twoRowSourcePunctureLocator_natDegree6401] at hdegree
  exact hdegree.trans hcaps.1
theorem recursiveAdjacentOrbit_weightedError_fixed_off_twoRowPuncture6401
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
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0) :
    (twoRowSourceBadCoordinates6401 W).card ≤ 22507 ∧
      (∀ i, i ∉ twoRowSourceBadCoordinates6401 W →
        sigma (adjacentOrbitWeightedFullError6401 W B z i) =
          adjacentOrbitWeightedFullError6401 W B z i) ∧
      (∀ i, adjacentOrbitWeightedFullError6401 W B z i ≠ 0 ↔
        fullOwnerError6401 W z i ≠ 0) := by
  have hfull := recursiveFixedFailureRelation_twoRow_fullDomain6401
    W R G A B hzero hone hsigma hfixed z hz hGz
  refine ⟨twoRowSourceBadCoordinates_card_le_22507_of_terminalLanes6401
      W R G A B hG hA hB hzero hone, ?_, ?_⟩
  · intro i hi
    have hDne := twoRowSourcePunctureLocator_eval_ne_zero6401 W i hi
    have haugmented := hfull i
    simp only [Polynomial.eval_mul] at haugmented
    have hrelation : A.eval (alpha i) *
          sigma (fullOwnerError6401 W z i) =
        B.eval (alpha i) * fullOwnerError6401 W z i := by
      apply mul_left_cancel₀ hDne
      simpa only [mul_assoc] using haugmented
    exact adjacentOrbit_weightedError_fixed6401 sigma (alpha i)
      (fullOwnerError6401 W z i) A B (hfixed i) hadjacent hrelation
  · intro i
    have hBne := adjacentOrbit_rightEval_ne_zero_of_isCoprime6401
      sigma (alpha i) A B (hfixed i) hadjacent hcoprime
    change B.eval (alpha i) * fullOwnerError6401 W z i ≠ 0 ↔
      fullOwnerError6401 W z i ≠ 0
    constructor
    · intro hproduct herror
      exact hproduct (by rw [herror, mul_zero])
    · exact fun herror ↦ mul_ne_zero hBne herror
theorem exists_recursiveTerminal_nonAdjacent_or_weightedErrorFixed6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (hresultant : R.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 R.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 R.laneOne6401)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) :
    ∃ G A B : F[X],
      G ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ IsCoprime A B ∧
        polynomialFrobeniusNormSix sigma A =
          polynomialFrobeniusNormSix sigma B ∧
        A.natDegree ≤ homogeneousDirectionCap6401 ∧
        B.natDegree ≤ homogeneousDirectionCap6401 ∧
        R.laneZero6401 = Polynomial.C G * A.map Polynomial.C ∧
        R.laneOne6401 = Polynomial.C G * B.map Polynomial.C ∧
        (A ≠ B.map sigma ∨
          ((twoRowSourceBadCoordinates6401 W).card ≤ 22507 ∧
            ∀ z ∈ R.goodChallenges6401, G.eval z ≠ 0 →
              (∀ i, i ∉ twoRowSourceBadCoordinates6401 W →
                sigma (adjacentOrbitWeightedFullError6401 W B z i) =
                  adjacentOrbitWeightedFullError6401 W B z i) ∧
              (∀ i,
                adjacentOrbitWeightedFullError6401 W B z i ≠ 0 ↔
                  fullOwnerError6401 W z i ≠ 0))) := by
  obtain ⟨G, A, B, hG, hA, hB, hcoprime, hnormFixed,
      hAdegree, hBdegree, hzero, hone, _hpunctured⟩ :=
    exists_recursiveTerminalPuncturedCoprimeNormFixedPair6401
      W R hresultant hnorm horder hsigma hfixed
  refine ⟨G, A, B, hG, hA, hB, hcoprime, hnormFixed,
    hAdegree, hBdegree, hzero, hone, ?_⟩
  by_cases hadjacent : A = B.map sigma
  · right
    have hcard := twoRowSourceBadCoordinates_card_le_22507_of_terminalLanes6401
      W R G A B hG hA hB hzero hone
    refine ⟨hcard, ?_⟩
    intro z hz hGz
    have howner :=
      recursiveAdjacentOrbit_weightedError_fixed_off_twoRowPuncture6401
        W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
          z hz hGz
    exact ⟨howner.2.1, howner.2.2⟩
  · exact Or.inl hadjacent
end TwoRowTerminalLift
section FixedSupportSyndromeAudit
variable {F : Type} {I : Type*} [Field F] [DecidableEq F]
  [Fintype I] [DecidableEq I]
theorem weightedSyndrome_frobeniusDefect_eq_fixedSupport6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (y : I → F) (H : Finset I)
    (hfixedOff : ∀ i, i ∉ H → sigma (y i) = y i)
    (j : Nat) :
    sigma (weightedSyndrome alpha y j) - weightedSyndrome alpha y j =
      ∑ i ∈ H, syndromeWeight alpha i * alpha i ^ j *
        (sigma (y i) - y i) := by
  rw [sigma_weightedSyndrome sigma alpha hfixed y j]
  simp only [weightedSyndrome, Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ i, (syndromeWeight alpha i * alpha i ^ j * sigma (y i) -
        syndromeWeight alpha i * alpha i ^ j * y i) =
        ∑ i, syndromeWeight alpha i * alpha i ^ j *
          (sigma (y i) - y i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i ∈ H, syndromeWeight alpha i * alpha i ^ j *
          (sigma (y i) - y i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ H)
      intro i _hi hiH
      rw [hfixedOff i hiH, sub_self, mul_zero]
theorem recursiveAdjacentOrbit_weightedSyndromeDefect_supported6401
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {Owner : F → Polynomial F}
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
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ (R.goodChallenges6401 : Finset F))
    (hGz : G.eval z ≠ 0) (j : Nat) :
    sigma (weightedSyndrome alpha
        (adjacentOrbitWeightedFullError6401
          (sigma := sigma) (alpha := alpha) W B z) j) -
        weightedSyndrome alpha
          (adjacentOrbitWeightedFullError6401
            (sigma := sigma) (alpha := alpha) W B z) j =
      ∑ i ∈ twoRowSourceBadCoordinates6401 W,
        syndromeWeight alpha i * alpha i ^ j *
          (sigma (B.eval (alpha i) *
              @fullOwnerError6401 F _ _ sigma alpha u0 u1 S Aset Owner
                W z i) -
            B.eval (alpha i) *
              @fullOwnerError6401 F _ _ sigma alpha u0 u1 S Aset Owner
                W z i) := by
  have howner :=
    recursiveAdjacentOrbit_weightedError_fixed_off_twoRowPuncture6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
        z hz hGz
  exact weightedSyndrome_frobeniusDefect_eq_fixedSupport6401
    sigma alpha hfixed (adjacentOrbitWeightedFullError6401
      (sigma := sigma) (alpha := alpha) W B z)
      (twoRowSourceBadCoordinates6401 W) howner.2.1 j
end FixedSupportSyndromeAudit
end BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
end ProximityPrize.SubmissionLower

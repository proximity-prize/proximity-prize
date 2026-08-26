import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailFixedPairGlobalKernel6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTwoRowTailGlobalKernel6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRank6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFixedLaneRecurrence6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSFrobeniusTailKernelSufficiency6401
open BCHKSFrobeniusTailFailureSpace6401
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailFixedPairGlobalKernel6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section TailGlobalization
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
local instance : Nonempty (Fin n6401) :=
  ⟨⟨0, by native_decide⟩⟩
def PrimitiveLaneOrbitCrossCoprime6401
    (sigma : F →+* F) (U0 U1 : F[X]) : Prop :=
  IsCoprime U0 (U1.map sigma)
noncomputable def twoRowAugmentedTailPair6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hU0 : (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
      homogeneousDirectionCap6401)
    (hU1 : (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
      homogeneousDirectionCap6401)
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    Polynomial.degreeLT F (homogeneousDirectionCap6401 + 1) ×
      Polynomial.degreeLT F (homogeneousDirectionCap6401 + 1) :=
  (⟨twoRowSourcePunctureLocator6401 W * U0, by
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.natDegree_lt_iff_degree_lt hne0).1
        (hU0.trans_lt (Nat.lt_succ_self _))⟩,
    ⟨twoRowSourcePunctureLocator6401 W * U1, by
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.natDegree_lt_iff_degree_lt hne1).1
        (hU1.trans_lt (Nat.lt_succ_self _))⟩)
noncomputable def twoRowAugmentedTailVector6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hU0 : (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
      homogeneousDirectionCap6401)
    (hU1 : (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
      homogeneousDirectionCap6401)
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    Fin (homogeneousDirectionCap6401 + 1) ⊕
        Fin (homogeneousDirectionCap6401 + 1) → F :=
  boundedPairTailEquiv6401 homogeneousDirectionCap6401
    (twoRowAugmentedTailPair6401 W U0 U1 hU0 hU1 hne0 hne1)
theorem tailPairPolynomial_twoRowAugmentedTailVector6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hU0 : (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
      homogeneousDirectionCap6401)
    (hU1 : (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
      homogeneousDirectionCap6401)
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    tailPairPolynomial homogeneousDirectionCap6401
        (twoRowAugmentedTailVector6401 W U0 U1 hU0 hU1 hne0 hne1) =
      (twoRowSourcePunctureLocator6401 W * U0,
        twoRowSourcePunctureLocator6401 W * U1) := by
  exact tailPairPolynomial_boundedPairTailEquiv6401
    homogeneousDirectionCap6401
      (twoRowAugmentedTailPair6401 W U0 U1 hU0 hU1 hne0 hne1)
theorem twoRowAugmentedTailVector_ne_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hU0 : (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
      homogeneousDirectionCap6401)
    (hU1 : (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
      homogeneousDirectionCap6401)
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    twoRowAugmentedTailVector6401 W U0 U1 hU0 hU1 hne0 hne1 ≠ 0 := by
  intro hv
  have hpairzero :
      twoRowAugmentedTailPair6401 W U0 U1 hU0 hU1 hne0 hne1 = 0 := by
    apply (boundedPairTailEquiv6401 homogeneousDirectionCap6401).injective
    rw [map_zero]
    exact hv
  have hleft := congrArg (fun Q ↦ Q.1.1) hpairzero
  exact hne0 hleft
private theorem receivedMinusOwner_failureRelation6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (z : F) (A B : F[X])
    (hfailure : TwoLaneFailureRelation sigma alpha
      (fullOwnerError6401 W z) A B) :
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u0 i + z * u1 i - (Owner z).eval (alpha i)) A B := by
  intro i
  have hi := hfailure i
  change A.eval (alpha i) *
      sigma ((Owner z).eval (alpha i) - (u0 i + z * u1 i)) =
    B.eval (alpha i) *
      ((Owner z).eval (alpha i) - (u0 i + z * u1 i)) at hi
  change A.eval (alpha i) *
      sigma (u0 i + z * u1 i - (Owner z).eval (alpha i)) =
    B.eval (alpha i) *
      (u0 i + z * u1 i - (Owner z).eval (alpha i))
  rw [show u0 i + z * u1 i - (Owner z).eval (alpha i) =
    -((Owner z).eval (alpha i) - (u0 i + z * u1 i)) by ring, map_neg]
  linear_combination -hi
theorem recursiveTwoRow_owner_semanticTailKernel6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0ne : U0 ≠ 0) (hU1ne : U1 ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0)
    (hPdegree : (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hagreement : ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i) :
    let hdegrees :=
      twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
        W R G U0 U1 hG hU0ne hU1ne hzero hone
    let hL := twoRowSourcePunctureLocator_ne_zero6401 W
    let v := twoRowAugmentedTailVector6401 W U0 U1
      hdegrees.1 hdegrees.2 (mul_ne_zero hL hU0ne) (mul_ne_zero hL hU1ne)
    (receivedTailMatrix6401 sigma alpha
      (fun i ↦ u0 i + z * u1 i)
      ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec v = 0 := by
  dsimp only
  let retained := Aset z \ W.sourcePuncture.badCoordinates
  have hagreeRetained : ∀ i ∈ retained,
      (Owner z).eval (alpha i) = u0 i + z * u1 i := by
    intro i hi
    exact hagreement i (Finset.mem_sdiff.mp hi).1
  have hretained := R.retained_agreements6401 z hz
  have hroots : ownerDegreeCap6401 + homogeneousDirectionCap6401 <
      retained.card := by
    exact (show ownerDegreeCap6401 + homogeneousDirectionCap6401 <
      primitiveSourceWindow6401 by native_decide).trans_le hretained
  have hwindow : ownerDegreeCap6401 + homogeneousDirectionCap6401 <
      Fintype.card (Fin n6401) := by native_decide
  have hdegrees :=
    twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G U0 U1 hG hU0ne hU1ne hzero hone
  have hL := twoRowSourcePunctureLocator_ne_zero6401 W
  let v := twoRowAugmentedTailVector6401 W U0 U1
    hdegrees.1 hdegrees.2 (mul_ne_zero hL hU0ne) (mul_ne_zero hL hU1ne)
  apply (receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    sigma alpha (fun i ↦ u0 i + z * u1 i)
      ownerDegreeCap6401 homogeneousDirectionCap6401 v hwindow).2
  rw [tailPairPolynomial_twoRowAugmentedTailVector6401]
  apply (receivedPairInterpolant_degree_iff_failureRelation6401
    sigma alpha (fun i ↦ u0 i + z * u1 i) (Owner z)
      (twoRowSourcePunctureLocator6401 W * U0)
      (twoRowSourcePunctureLocator6401 W * U1) retained
      ownerDegreeCap6401 homogeneousDirectionCap6401
      hfixed hagreeRetained hPdegree hdegrees.1 hdegrees.2
      hwindow hroots).2
  apply receivedMinusOwner_failureRelation6401 W z
  exact recursiveFixedFailureRelation_twoRow_fullDomain6401
    W R G U0 U1 hzero hone hsigma hfixed z hz hGz
theorem twoRowSourcePunctureLocator_dvd_of_eval_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (Q : F[X])
    (hzero : ∀ i ∈ twoRowSourceBadCoordinates6401 W,
      Q.eval (alpha i) = 0) :
    twoRowSourcePunctureLocator6401 W ∣ Q := by
  classical
  unfold twoRowSourcePunctureLocator6401
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C alpha.injective hij
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero i hi
theorem twoRowPunctureLocator_dvd_slopeRepresentatives6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X]) :
    twoRowSourcePunctureLocator6401 W ∣
        receivedPairInterpolant6401 sigma alpha u1
          (twoRowSourcePunctureLocator6401 W * U0) 0 ∧
      twoRowSourcePunctureLocator6401 W ∣
        receivedPairInterpolant6401 sigma alpha u1 0
          (twoRowSourcePunctureLocator6401 W * U1) := by
  constructor
  · apply twoRowSourcePunctureLocator_dvd_of_eval_zero6401 W
    intro i hi
    rw [receivedPairInterpolant_eval6401]
    have hroot := twoRowSourcePunctureLocator_eval_eq_zero6401 W i hi
    simp [Polynomial.eval_mul, hroot]
  · apply twoRowSourcePunctureLocator_dvd_of_eval_zero6401 W
    intro i hi
    rw [receivedPairInterpolant_eval6401]
    have hroot := twoRowSourcePunctureLocator_eval_eq_zero6401 W i hi
    simp [Polynomial.eval_mul, hroot]
theorem exists_recursiveTwoRowFixedPair_globalTailKernel6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (hresultant : R.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 R.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 R.laneOne6401)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hPdegree : ∀ z ∈ R.goodChallenges6401,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hagreement : ∀ z ∈ R.goodChallenges6401, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i) :
    ∃ G U0 U1 : F[X],
      ∃ v : Fin (homogeneousDirectionCap6401 + 1) ⊕
          Fin (homogeneousDirectionCap6401 + 1) → F,
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧ v ≠ 0 ∧
      R.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
      R.laneOne6401 = Polynomial.C G * U1.map Polynomial.C ∧
      (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
        homogeneousDirectionCap6401 ∧
      (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
        homogeneousDirectionCap6401 ∧
      tailPairPolynomial homogeneousDirectionCap6401 v =
        (twoRowSourcePunctureLocator6401 W * U0,
          twoRowSourcePunctureLocator6401 W * U1) ∧
      (twoRowSourcePunctureLocator6401 W ∣
        receivedPairInterpolant6401 sigma alpha u1
          (twoRowSourcePunctureLocator6401 W * U0) 0) ∧
      (twoRowSourcePunctureLocator6401 W ∣
        receivedPairInterpolant6401 sigma alpha u1 0
          (twoRowSourcePunctureLocator6401 W * U1)) ∧
      ∀ T : Finset F, T ⊆ R.goodChallenges6401 →
        (∀ z ∈ T, G.eval z ≠ 0) → q6401 < T.card →
        (∀ z ∈ T,
          (receivedTailMatrix6401 sigma alpha
            (fun i ↦ u0 i + z * u1 i)
            ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec v = 0) ∧
        (receivedTailMatrixZ6401 sigma alpha u0 u1 q6401
          ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec
            (fun c ↦ Polynomial.C (v c)) = 0 ∧
        ((receivedTailMatrix6401 sigma alpha u0
          ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec v = 0 ∧
          (receivedTailMatrix6401 sigma alpha u1
            ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec
              (leftTailVector6401 v) = 0 ∧
          (receivedTailMatrix6401 sigma alpha u1
            ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec
              (rightTailVector6401 v) = 0) ∧
        ((receivedPairInterpolant6401 sigma alpha u0
          (tailPairPolynomial homogeneousDirectionCap6401 v).1
          (tailPairPolynomial homogeneousDirectionCap6401 v).2).natDegree
            ≤ ownerDegreeCap6401 + homogeneousDirectionCap6401 ∧
          (receivedPairInterpolant6401 sigma alpha u1
            (tailPairPolynomial homogeneousDirectionCap6401 v).1 0).natDegree
            ≤ ownerDegreeCap6401 + homogeneousDirectionCap6401 ∧
          (receivedPairInterpolant6401 sigma alpha u1 0
            (tailPairPolynomial homogeneousDirectionCap6401 v).2).natDegree
            ≤ ownerDegreeCap6401 + homogeneousDirectionCap6401) := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hzero, hone, _hpunctured⟩ :=
    exists_recursiveCommonContentFixedFailurePair6401
      W R hresultant hnorm horder hsigma hfixed
  have hdegrees :=
    twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone
  have hL := twoRowSourcePunctureLocator_ne_zero6401 W
  have hAne := mul_ne_zero hL hU0
  have hBne := mul_ne_zero hL hU1
  let v := twoRowAugmentedTailVector6401 W U0 U1
    hdegrees.1 hdegrees.2 hAne hBne
  have hv : v ≠ 0 := twoRowAugmentedTailVector_ne_zero6401
    W U0 U1 hdegrees.1 hdegrees.2 hAne hBne
  have hvPair := tailPairPolynomial_twoRowAugmentedTailVector6401
    W U0 U1 hdegrees.1 hdegrees.2 hAne hBne
  have hslopeDiv := twoRowPunctureLocator_dvd_slopeRepresentatives6401
    W U0 U1
  refine ⟨G, U0, U1, v, hG, hU0, hU1, hv, hzero, hone,
    hdegrees.1, hdegrees.2, hvPair, hslopeDiv.1, hslopeDiv.2, ?_⟩
  intro T hTgood hTG hmass
  have hkernel : ∀ z ∈ T,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u0 i + z * u1 i)
        ownerDegreeCap6401 homogeneousDirectionCap6401).mulVec v = 0 := by
    intro z hz
    have hzgood := hTgood hz
    exact recursiveTwoRow_owner_semanticTailKernel6401
      W R G U0 U1 hG hU0 hU1 hzero hone hsigma hfixed
        z hzgood (hTG z hz) (hPdegree z hzgood)
          (hagreement z hzgood)
  have hglobal :=
    receivedTailMatrixZ_mulVec_C_eq_zero_of_fixedKernels6401
      sigma alpha u0 u1 q6401 ownerDegreeCap6401
        homogeneousDirectionCap6401 (by native_decide) T
          (fun z _hz ↦ hsigma z) v hkernel hmass
  have hthree := receivedTail_fixedPair_threeKernels_of_graphKernel6401
    sigma alpha u0 u1 q6401 ownerDegreeCap6401
      homogeneousDirectionCap6401 (by native_decide) v hglobal
  have hproducts :=
    receivedTail_fixedPair_threeProductDegrees_of_manyOwners6401
      sigma alpha u0 u1 q6401 ownerDegreeCap6401
        homogeneousDirectionCap6401 (by native_decide) T
          (fun z _hz ↦ hsigma z) v hkernel hmass (by native_decide)
  exact ⟨hkernel, hglobal, hthree, hproducts⟩
end TailGlobalization
end BCHKSExtremePrimitiveTwoRowTailGlobalKernel6401
end ProximityPrize.SubmissionLower

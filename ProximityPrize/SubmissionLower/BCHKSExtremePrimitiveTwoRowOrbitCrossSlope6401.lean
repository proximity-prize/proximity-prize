import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTwoRowTailGlobalKernel6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveOrbitCrossAlgebra6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAdjacentOrbitDivisibleCurve6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFullReceivedSlopeClosure6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTwoRowOrbitCrossSlope6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveTerminalCommonContentCoprime6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveTwoRowTailGlobalKernel6401
open BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
open BCHKSExtremePrimitiveOrbitCrossAlgebra6401
open BCHKSExtremePrimitiveAdjacentOrbitDivisibleCurve6401
open BCHKSExtremePrimitiveFullReceivedSlopeClosure6401
open BCHKSFrobeniusTailKernelSufficiency6401
open BCHKSFrobeniusTailFailureSpace6401
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailFixedPairGlobalKernel6401
open BCHKSSubfieldFrobenius6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
section OrbitCrossSlope
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
local instance : Nonempty (Fin n6401) :=
  ⟨⟨0, by native_decide⟩⟩
noncomputable def twoRowAdaptiveTailDegree6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X]) : Nat :=
  max (twoRowSourcePunctureLocator6401 W * U0).natDegree
    (twoRowSourcePunctureLocator6401 W * U1).natDegree
noncomputable def twoRowAdaptiveTailPair6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    Polynomial.degreeLT F (twoRowAdaptiveTailDegree6401 W U0 U1 + 1) ×
      Polynomial.degreeLT F
        (twoRowAdaptiveTailDegree6401 W U0 U1 + 1) :=
  (⟨twoRowSourcePunctureLocator6401 W * U0, by
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.natDegree_lt_iff_degree_lt hne0).1
        ((le_max_left _ _).trans_lt (Nat.lt_succ_self _))⟩,
    ⟨twoRowSourcePunctureLocator6401 W * U1, by
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.natDegree_lt_iff_degree_lt hne1).1
        ((le_max_right _ _).trans_lt (Nat.lt_succ_self _))⟩)
noncomputable def twoRowAdaptiveTailVector6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    Fin (twoRowAdaptiveTailDegree6401 W U0 U1 + 1) ⊕
        Fin (twoRowAdaptiveTailDegree6401 W U0 U1 + 1) → F :=
  boundedPairTailEquiv6401 (twoRowAdaptiveTailDegree6401 W U0 U1)
    (twoRowAdaptiveTailPair6401 W U0 U1 hne0 hne1)
theorem tailPairPolynomial_twoRowAdaptiveTailVector6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hne0 : twoRowSourcePunctureLocator6401 W * U0 ≠ 0)
    (hne1 : twoRowSourcePunctureLocator6401 W * U1 ≠ 0) :
    tailPairPolynomial (twoRowAdaptiveTailDegree6401 W U0 U1)
        (twoRowAdaptiveTailVector6401 W U0 U1 hne0 hne1) =
      (twoRowSourcePunctureLocator6401 W * U0,
        twoRowSourcePunctureLocator6401 W * U1) := by
  exact tailPairPolynomial_boundedPairTailEquiv6401
    (twoRowAdaptiveTailDegree6401 W U0 U1)
      (twoRowAdaptiveTailPair6401 W U0 U1 hne0 hne1)
theorem twoRowAdaptiveTailDegree_le_22507_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C) :
    twoRowAdaptiveTailDegree6401 W U0 U1 ≤
      homogeneousDirectionCap6401 := by
  exact max_le
    (twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone).1
    (twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone).2
theorem twoRowSourcePunctureLocator_map_eq_self6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) :
    (twoRowSourcePunctureLocator6401 W).map sigma =
      twoRowSourcePunctureLocator6401 W := by
  classical
  simp only [twoRowSourcePunctureLocator6401, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hfixed i]
theorem twoRowSourcePunctureLocator_eval_ne_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (i : Fin n6401) (hi : i ∉ twoRowSourceBadCoordinates6401 W) :
    (twoRowSourcePunctureLocator6401 W).eval (alpha i) ≠ 0 := by
  classical
  simp only [twoRowSourcePunctureLocator6401, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply sub_ne_zero.mpr
  intro hij
  have heq : i = j := alpha.injective hij
  subst j
  exact hi hj
theorem recursiveTwoRow_owner_adaptiveTailKernel6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
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
    let v := twoRowAdaptiveTailVector6401 W U0 U1
      (mul_ne_zero (twoRowSourcePunctureLocator_ne_zero6401 W) hU0)
      (mul_ne_zero (twoRowSourcePunctureLocator_ne_zero6401 W) hU1)
    (receivedTailMatrix6401 sigma alpha
      (fun i ↦ u0 i + z * u1 i) ownerDegreeCap6401
      (twoRowAdaptiveTailDegree6401 W U0 U1)).mulVec v = 0 := by
  dsimp only
  let retained := Aset z \ W.sourcePuncture.badCoordinates
  have hagreeRetained : ∀ i ∈ retained,
      (Owner z).eval (alpha i) = u0 i + z * u1 i := by
    intro i hi
    exact hagreement i (Finset.mem_sdiff.mp hi).1
  have hretained := R.retained_agreements6401 z hz
  have hretained' : primitiveSourceWindow6401 ≤ retained.card := by
    simpa [retained] using hretained
  have hd := twoRowAdaptiveTailDegree_le_22507_6401
    W R G U0 U1 hG hU0 hU1 hzero hone
  have hroots : ownerDegreeCap6401 +
      twoRowAdaptiveTailDegree6401 W U0 U1 < retained.card := by
    have hmargin : ownerDegreeCap6401 + homogeneousDirectionCap6401 <
        primitiveSourceWindow6401 := by native_decide
    exact ((Nat.add_le_add_left hd ownerDegreeCap6401).trans_lt hmargin).trans_le
      hretained'
  have hwindow : ownerDegreeCap6401 +
      twoRowAdaptiveTailDegree6401 W U0 U1 < Fintype.card (Fin n6401) := by
    have : ownerDegreeCap6401 + homogeneousDirectionCap6401 < n6401 := by
      native_decide
    simpa using (Nat.add_le_add_left hd ownerDegreeCap6401).trans_lt this
  have hH := twoRowSourcePunctureLocator_ne_zero6401 W
  have hA := mul_ne_zero hH hU0
  have hB := mul_ne_zero hH hU1
  let v := twoRowAdaptiveTailVector6401 W U0 U1 hA hB
  apply (receivedTailMatrix_mulVec_eq_zero_iff_degree6401
    sigma alpha (fun i ↦ u0 i + z * u1 i) ownerDegreeCap6401
      (twoRowAdaptiveTailDegree6401 W U0 U1) v hwindow).2
  rw [tailPairPolynomial_twoRowAdaptiveTailVector6401]
  apply (receivedPairInterpolant_degree_iff_failureRelation6401
    sigma alpha (fun i ↦ u0 i + z * u1 i) (Owner z)
      (twoRowSourcePunctureLocator6401 W * U0)
      (twoRowSourcePunctureLocator6401 W * U1) retained
      ownerDegreeCap6401 (twoRowAdaptiveTailDegree6401 W U0 U1)
      hfixed hagreeRetained hPdegree (le_max_left _ _) (le_max_right _ _)
      hwindow hroots).2
  intro i
  have hi := recursiveFixedFailureRelation_twoRow_fullDomain6401
    W R G U0 U1 hzero hone hsigma hfixed z hz hGz i
  change (twoRowSourcePunctureLocator6401 W * U0).eval (alpha i) *
      sigma (u0 i + z * u1 i - (Owner z).eval (alpha i)) =
    (twoRowSourcePunctureLocator6401 W * U1).eval (alpha i) *
      (u0 i + z * u1 i - (Owner z).eval (alpha i))
  change (twoRowSourcePunctureLocator6401 W * U0).eval (alpha i) *
      sigma ((Owner z).eval (alpha i) - (u0 i + z * u1 i)) =
    (twoRowSourcePunctureLocator6401 W * U1).eval (alpha i) *
      ((Owner z).eval (alpha i) - (u0 i + z * u1 i)) at hi
  rw [show u0 i + z * u1 i - (Owner z).eval (alpha i) =
    -((Owner z).eval (alpha i) - (u0 i + z * u1 i)) by ring, map_neg]
  linear_combination -hi
theorem recursiveTwoRow_adaptiveThreeProductDegrees6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (T : Finset F) (hTgood : T ⊆ R.goodChallenges6401)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hmass : q6401 < T.card)
    (hPdegree : ∀ z ∈ T,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hagreement : ∀ z ∈ T, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i) :
    let H := twoRowSourcePunctureLocator6401 W
    let d := twoRowAdaptiveTailDegree6401 W U0 U1
    (receivedPairInterpolant6401 sigma alpha u0 (H * U0) (H * U1)).natDegree
        ≤ ownerDegreeCap6401 + d ∧
      (receivedPairInterpolant6401 sigma alpha u1 (H * U0) 0).natDegree
        ≤ ownerDegreeCap6401 + d ∧
      (receivedPairInterpolant6401 sigma alpha u1 0 (H * U1)).natDegree
        ≤ ownerDegreeCap6401 + d := by
  dsimp only
  have hH := twoRowSourcePunctureLocator_ne_zero6401 W
  have hA := mul_ne_zero hH hU0
  have hB := mul_ne_zero hH hU1
  let d := twoRowAdaptiveTailDegree6401 W U0 U1
  let v := twoRowAdaptiveTailVector6401 W U0 U1 hA hB
  have hkernel : ∀ z ∈ T,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u0 i + z * u1 i) ownerDegreeCap6401 d).mulVec v = 0 := by
    intro z hz
    exact recursiveTwoRow_owner_adaptiveTailKernel6401
      W R G U0 U1 hG hU0 hU1 hzero hone hsigma hfixed z
        (hTgood hz) (hTG z hz) (hPdegree z hz) (hagreement z hz)
  have hwindow : ownerDegreeCap6401 + d < Fintype.card (Fin n6401) := by
    have hd := twoRowAdaptiveTailDegree_le_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone
    have hn : ownerDegreeCap6401 + homogeneousDirectionCap6401 < n6401 := by
      native_decide
    exact (Nat.add_le_add_left hd ownerDegreeCap6401).trans_lt hn
  have hvPair : tailPairPolynomial d v =
      (twoRowSourcePunctureLocator6401 W * U0,
        twoRowSourcePunctureLocator6401 W * U1) := by
    dsimp [d, v]
    exact tailPairPolynomial_twoRowAdaptiveTailVector6401 W U0 U1 hA hB
  exact receivedTail_threeProductDegrees_of_decodedPair6401
    sigma alpha u0 u1 q6401 ownerDegreeCap6401 d (by native_decide)
      T (fun z _hz ↦ hsigma z) v
      (twoRowSourcePunctureLocator6401 W * U0)
      (twoRowSourcePunctureLocator6401 W * U1) hvPair hkernel hmass hwindow
set_option maxHeartbeats 4000000 in
theorem twoRowAdaptiveSlope_crossIdentity6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hleftDegree :
      (receivedPairInterpolant6401 sigma alpha u1
        (twoRowSourcePunctureLocator6401 W * U0) 0).natDegree ≤
          ownerDegreeCap6401 + twoRowAdaptiveTailDegree6401 W U0 U1)
    (hrightDegree :
      (receivedPairInterpolant6401 sigma alpha u1 0
        (twoRowSourcePunctureLocator6401 W * U1)).natDegree ≤
          ownerDegreeCap6401 + twoRowAdaptiveTailDegree6401 W U0 U1)
    (hdCap : twoRowAdaptiveTailDegree6401 W U0 U1 ≤
      homogeneousDirectionCap6401) :
    receivedPairInterpolant6401 sigma alpha u1
        (twoRowSourcePunctureLocator6401 W * U0) 0 *
          (twoRowSourcePunctureLocator6401 W * U1).map sigma =
      (twoRowSourcePunctureLocator6401 W * U0) *
        (-receivedPairInterpolant6401 sigma alpha u1 0
          (twoRowSourcePunctureLocator6401 W * U1)).map sigma := by
  have hdA : (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
      twoRowAdaptiveTailDegree6401 W U0 U1 := le_max_left _ _
  have hdB : (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
      twoRowAdaptiveTailDegree6401 W U0 U1 := le_max_right _ _
  have hLeval : ∀ i,
      (receivedPairInterpolant6401 sigma alpha u1
        (twoRowSourcePunctureLocator6401 W * U0) 0).eval (alpha i) =
      (twoRowSourcePunctureLocator6401 W * U0).eval (alpha i) *
        sigma (u1 i) := by
    intro i
    simpa only [receivedPairInterpolant_eval6401, Polynomial.eval_zero,
      mul_zero, zero_mul, sub_zero]
  have hReval : ∀ i,
      (-receivedPairInterpolant6401 sigma alpha u1 0
        (twoRowSourcePunctureLocator6401 W * U1)).eval (alpha i) =
      (twoRowSourcePunctureLocator6401 W * U1).eval (alpha i) * u1 i := by
    intro i
    simp only [Polynomial.eval_neg, receivedPairInterpolant_eval6401,
      Polynomial.eval_zero, zero_mul, zero_sub, neg_neg]
  have hRDeg :
      (-receivedPairInterpolant6401 sigma alpha u1 0
        (twoRowSourcePunctureLocator6401 W * U1)).natDegree ≤
        ownerDegreeCap6401 +
      twoRowAdaptiveTailDegree6401 W U0 U1 := by
    simpa using hrightDegree
  have htotal : ownerDegreeCap6401 + homogeneousDirectionCap6401 +
      homogeneousDirectionCap6401 < Fintype.card (Fin n6401) := by
    native_decide
  exact slopeInterpolants_cross_of_uniformDegreeCaps6401
    (F := F) (I := Fin n6401) sigma alpha hfixed u1
      (twoRowSourcePunctureLocator6401 W * U0)
      (twoRowSourcePunctureLocator6401 W * U1)
      (receivedPairInterpolant6401 sigma alpha u1
        (twoRowSourcePunctureLocator6401 W * U0) 0)
      (-receivedPairInterpolant6401 sigma alpha u1 0
        (twoRowSourcePunctureLocator6401 W * U1))
      ownerDegreeCap6401 (twoRowAdaptiveTailDegree6401 W U0 U1)
      homogeneousDirectionCap6401 hLeval hReval hleftDegree hRDeg
      hdA hdB hdCap htotal
theorem exists_primitiveSlopeFactorization_of_adaptiveProducts_of_orbitCross6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hcop : IsCoprime U0 U1)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hleftDegree :
      (receivedPairInterpolant6401 sigma alpha u1
        (twoRowSourcePunctureLocator6401 W * U0) 0).natDegree ≤
          ownerDegreeCap6401 + twoRowAdaptiveTailDegree6401 W U0 U1)
    (hrightDegree :
      (receivedPairInterpolant6401 sigma alpha u1 0
        (twoRowSourcePunctureLocator6401 W * U1)).natDegree ≤
          ownerDegreeCap6401 + twoRowAdaptiveTailDegree6401 W U0 U1)
    (hdCap : twoRowAdaptiveTailDegree6401 W U0 U1 ≤
      homogeneousDirectionCap6401)
    (horbit : PrimitiveLaneOrbitCrossCoprime6401 sigma U0 U1) :
    ∃ V : F[X], V.natDegree ≤ ownerDegreeCap6401 ∧
      receivedPairInterpolant6401 sigma alpha u1
          (twoRowSourcePunctureLocator6401 W * U0) 0 =
        twoRowSourcePunctureLocator6401 W * (U0 * V.map sigma) ∧
      -receivedPairInterpolant6401 sigma alpha u1 0
          (twoRowSourcePunctureLocator6401 W * U1) =
        twoRowSourcePunctureLocator6401 W * (U1 * V) ∧
      ∀ i, i ∉ twoRowSourceBadCoordinates6401 W →
        V.eval (alpha i) = u1 i := by
  let H := twoRowSourcePunctureLocator6401 W
  have hH : H ≠ 0 := twoRowSourcePunctureLocator_ne_zero6401 W
  have hLeval : ∀ i,
      (receivedPairInterpolant6401 sigma alpha u1 (H * U0) 0).eval
        (alpha i) =
      (H * U0).eval (alpha i) * sigma (u1 i) := by
    intro i
    simpa only [receivedPairInterpolant_eval6401, Polynomial.eval_zero,
      mul_zero, zero_mul, sub_zero]
  have hReval : ∀ i,
      (-receivedPairInterpolant6401 sigma alpha u1 0 (H * U1)).eval
        (alpha i) =
      (H * U1).eval (alpha i) * u1 i := by
    intro i
    simp only [Polynomial.eval_neg, receivedPairInterpolant_eval6401,
      Polynomial.eval_zero, zero_mul, zero_sub, neg_neg]
  have hRDeg :
      (-receivedPairInterpolant6401 sigma alpha u1 0 (H * U1)).natDegree ≤
        ownerDegreeCap6401 +
      twoRowAdaptiveTailDegree6401 W U0 U1 := by
    simpa only [H, Polynomial.natDegree_neg] using hrightDegree
  have hcross :
      receivedPairInterpolant6401 sigma alpha u1 (H * U0) 0 *
          (H * U1).map sigma =
        (H * U0) *
          (-receivedPairInterpolant6401 sigma alpha u1 0
            (H * U1)).map sigma := by
    simpa only [H] using
      twoRowAdaptiveSlope_crossIdentity6401 W U0 U1 hfixed
        hleftDegree hrightDegree hdCap
  have hLdiv :
      H ∣ receivedPairInterpolant6401 sigma alpha u1 (H * U0) 0 := by
    simpa only [H] using
      (twoRowPunctureLocator_dvd_slopeRepresentatives6401 W U0 U1).1
  obtain ⟨Rraw0, hRraw0⟩ :=
    (twoRowPunctureLocator_dvd_slopeRepresentatives6401 W U0 U1).2
  have hRdiv :
      H ∣ -receivedPairInterpolant6401 sigma alpha u1 0 (H * U1) := by
    refine ⟨-Rraw0, ?_⟩
    rw [show receivedPairInterpolant6401 sigma alpha u1 0 (H * U1) =
      H * Rraw0 by simpa only [H] using hRraw0]
    rw [mul_neg]
  have hHmap : H.map sigma = H :=
    twoRowSourcePunctureLocator_map_eq_self6401 W hfixed
  have hLDeg' :
      (receivedPairInterpolant6401 sigma alpha u1 (H * U0) 0).natDegree ≤
        ownerDegreeCap6401 +
      max (H * U0).natDegree (H * U1).natDegree := by
    simpa only [H, twoRowAdaptiveTailDegree6401] using hleftDegree
  have hRDeg' :
      (-receivedPairInterpolant6401 sigma alpha u1 0 (H * U1)).natDegree ≤
        ownerDegreeCap6401 +
      max (H * U0).natDegree (H * U1).natDegree := by
    simpa only [H, twoRowAdaptiveTailDegree6401] using hRDeg
  change IsCoprime U0 (U1.map sigma) at horbit
  obtain ⟨V, hVdegree, _hLfactor, _hRfactor, hVeval⟩ :=
    exists_commonSlopeFactor_of_invariantDivisibleCross6401
      H U0 U1
        (receivedPairInterpolant6401 sigma alpha u1 (H * U0) 0)
        (-receivedPairInterpolant6401 sigma alpha u1 0 (H * U1))
        ownerDegreeCap6401 hH hU0 hU1 hcop hHmap hcross hLdiv hRdiv
        hLDeg' hRDeg' horbit horder
  refine ⟨V, hVdegree, ?_, ?_, ?_⟩
  · simpa only [H] using _hLfactor
  · simpa only [H] using _hRfactor
  intro i hi
  have hHat : H.eval (alpha i) ≠ 0 :=
    twoRowSourcePunctureLocator_eval_ne_zero6401 W i hi
  exact hVeval (alpha i) (u1 i) (hfixed i) hHat (hLeval i) (hReval i)
theorem exists_primitiveSlope_of_adaptiveProducts_of_orbitCross6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U0 U1 : F[X])
    (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hcop : IsCoprime U0 U1)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hleftDegree :
      (receivedPairInterpolant6401 sigma alpha u1
        (twoRowSourcePunctureLocator6401 W * U0) 0).natDegree ≤
          ownerDegreeCap6401 + twoRowAdaptiveTailDegree6401 W U0 U1)
    (hrightDegree :
      (receivedPairInterpolant6401 sigma alpha u1 0
        (twoRowSourcePunctureLocator6401 W * U1)).natDegree ≤
          ownerDegreeCap6401 + twoRowAdaptiveTailDegree6401 W U0 U1)
    (hdCap : twoRowAdaptiveTailDegree6401 W U0 U1 ≤
      homogeneousDirectionCap6401)
    (horbit : PrimitiveLaneOrbitCrossCoprime6401 sigma U0 U1) :
    ∃ V : F[X], V.natDegree ≤ ownerDegreeCap6401 ∧
      ∀ i, i ∉ twoRowSourceBadCoordinates6401 W →
        V.eval (alpha i) = u1 i := by
  obtain ⟨V, hV, _hleft, _hright, heval⟩ :=
    exists_primitiveSlopeFactorization_of_adaptiveProducts_of_orbitCross6401
      W U0 U1 hU0 hU1 hcop hfixed horder hleftDegree hrightDegree
        hdCap horbit
  exact ⟨V, hV, heval⟩
theorem exists_terminalPrimitivePair_orbitCross_producesPuncturedSlope6401
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
    (T : Finset F) (hTgood : T ⊆ R.goodChallenges6401)
    (hmass : q6401 < T.card)
    (hPdegree : ∀ z ∈ T,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hagreement : ∀ z ∈ T, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧ IsCoprime U0 U1 ∧
      R.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
      R.laneOne6401 = Polynomial.C G * U1.map Polynomial.C ∧
      ((∀ z ∈ T, G.eval z ≠ 0) →
        PrimitiveLaneOrbitCrossCoprime6401 sigma U0 U1 →
        ∃ V : F[X], V.natDegree ≤ ownerDegreeCap6401 ∧
          ∀ i, i ∉ twoRowSourceBadCoordinates6401 W →
            V.eval (alpha i) = u1 i) := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hcop, hzero, hone⟩ :=
    exists_recursiveCommonContent_coprimeFixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
      R horder hresultant hnorm
  refine ⟨G, U0, U1, hG, hU0, hU1, hcop, hzero, hone, ?_⟩
  intro hTG horbit
  have hproducts := recursiveTwoRow_adaptiveThreeProductDegrees6401
    W R G U0 U1 hG hU0 hU1 hzero hone hsigma hfixed T hTgood hTG
      hmass hPdegree hagreement
  have hdCap := twoRowAdaptiveTailDegree_le_22507_6401
    W R G U0 U1 hG hU0 hU1 hzero hone
  exact exists_primitiveSlope_of_adaptiveProducts_of_orbitCross6401
    W U0 U1 hU0 hU1 hcop hfixed horder hproducts.2.1 hproducts.2.2
      hdCap horbit
theorem exists_fullReceivedSlope_of_terminalPair_orbitCross6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hcop : IsCoprime U0 U1)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C)
    (hU1degree : U1.natDegree = homogeneousDirectionCap6401)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (T : Finset F) (hTgood : T ⊆ R.goodChallenges6401)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hmass : q6401 < T.card)
    (hPdegree : ∀ z ∈ T,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hagreement : ∀ z ∈ T, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i)
    (horbit : PrimitiveLaneOrbitCrossCoprime6401 sigma U0 U1) :
    ∃ V : F[X], V.natDegree ≤ ownerDegreeCap6401 ∧
      ∀ i, V.eval (alpha i) = u1 i := by
  have hproducts := recursiveTwoRow_adaptiveThreeProductDegrees6401
    W R G U0 U1 hG hU0 hU1 hzero hone hsigma hfixed T hTgood hTG
      hmass hPdegree hagreement
  have hdCap := twoRowAdaptiveTailDegree_le_22507_6401
    W R G U0 U1 hG hU0 hU1 hzero hone
  obtain ⟨V, hVdegree, hVeval⟩ :=
    exists_primitiveSlope_of_adaptiveProducts_of_orbitCross6401
      W U0 U1 hU0 hU1 hcop hfixed horder hproducts.2.1 hproducts.2.2
        hdCap horbit
  have hbad : twoRowSourceBadCoordinates6401 W = ∅ :=
    twoRowSourceBadCoordinates_eq_empty_of_rightLane_degree_eq_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone hU1degree
  refine ⟨V, hVdegree, ?_⟩
  intro i
  apply hVeval i
  rw [hbad]
  simp
theorem polynomialAffineCurveWitness_of_terminalPair_orbitCross6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hcop : IsCoprime U0 U1)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C)
    (hU1degree : U1.natDegree = homogeneousDirectionCap6401)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (T : Finset F) (hTgood : T ⊆ R.goodChallenges6401)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hPdegree : ∀ z ∈ T,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ T, a6401 ≤ (Aset z).card)
    (hagreement : ∀ z ∈ T, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i)
    (hlarge : fullReceivedSlopeOwnerCap6401 < T.card)
    (horbit : PrimitiveLaneOrbitCrossCoprime6401 sigma U0 U1) :
    PolynomialAffineCurveWitness6401 T Owner := by
  have hqcap : q6401 < fullReceivedSlopeOwnerCap6401 := by
    native_decide
  have hmass : q6401 < T.card := hqcap.trans hlarge
  obtain ⟨V, hVdegree, hVeval⟩ :=
    exists_fullReceivedSlope_of_terminalPair_orbitCross6401
      W R G U0 U1 hG hU0 hU1 hcop hzero hone hU1degree horder hsigma
        hfixed T hTgood hTG hmass hPdegree hagreement horbit
  exact polynomialAffineCurveWitness_of_fullReceivedSlope6401
    alpha u0 u1 T Aset Owner V hVdegree hVeval hPdegree hrow
      hagreement hlarge
end OrbitCrossSlope
end BCHKSExtremePrimitiveTwoRowOrbitCrossSlope6401
end ProximityPrize.SubmissionLower

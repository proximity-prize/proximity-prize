import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalPunctureDerivativeIntegration6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTerminalPolynomialGaugeSourceAdapters6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitivePolynomialGaugeFullTail6401
open BCHKSExtremePrimitiveTerminalPunctureDerivativeIntegration6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section SourceAdapters
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem terminalPolynomialGaugeSource_reconstruction_on6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B K : F[X]) (T : Finset F)
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hKdegree : K.natDegree ≤ 5 * A.natDegree)
    (hTS : T ⊆ S)
    (hOwnerDegree : ∀ z ∈ S,
      (Owner z).natDegree ≤ ownerDegreeCap6401) :
    ∀ w ∈ T,
      twoRowSourcePunctureLocator6401 W * K * Owner w =
        fullWordInterpolant6401 alpha (fun j ↦
            (twoRowSourcePunctureLocator6401 W * K).eval (alpha j) *
              u0 j) +
          Polynomial.C w * fullWordInterpolant6401 alpha (fun j ↦
            (twoRowSourcePunctureLocator6401 W * K).eval (alpha j) *
              u1 j) +
          fullWordInterpolant6401 alpha (fun j ↦
            (twoRowSourcePunctureLocator6401 W * K).eval (alpha j) *
              ((Owner w).eval (alpha j) - (u0 j + w * u1 j))) := by
  have haugmentedA :
      (twoRowSourcePunctureLocator6401 W * A).natDegree ≤
        homogeneousDirectionCap6401 :=
    (twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G A B hG hA hB hzero hone).1
  intro w hw
  have hdegree :
      ((twoRowSourcePunctureLocator6401 W * K) * Owner w).natDegree <
        n6401 :=
    (twoRowPolynomialGauge_scaledOwner_natDegree_le_243606_6401
      (sigma := sigma) (alpha := alpha) (u0 := u0) (u1 := u1)
      (S := S) (Aset := Aset) (Owner := Owner)
      W A K w hA haugmentedA hKdegree
        (hOwnerDegree w (hTS hw))).trans_lt (by native_decide)
  exact twoRowPolynomialGauge_reconstructionIdentity6401
    (sigma := sigma) (alpha := alpha) (u0 := u0) (u1 := u1)
    (S := S) (Aset := Aset) (Owner := Owner) W K w hdegree
theorem terminalPolynomialGaugeSource_errorFixed_on6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B K : F[X]) (T : Finset F)
    (hcop : IsCoprime A B)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hgauge : B * K.map sigma = A * K)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hTgood : T ⊆ R.goodChallenges6401)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0) :
    ∀ w ∈ T,
      (fullWordInterpolant6401 alpha (fun j ↦
        (twoRowSourcePunctureLocator6401 W * K).eval (alpha j) *
          ((Owner w).eval (alpha j) - (u0 j + w * u1 j)))).map sigma =
      fullWordInterpolant6401 alpha (fun j ↦
        (twoRowSourcePunctureLocator6401 W * K).eval (alpha j) *
          ((Owner w).eval (alpha j) - (u0 j + w * u1 j))) := by
  intro w hw
  have hfailure := recursiveFixedFailureRelation_twoRow_fullDomain6401
    (sigma := sigma) (alpha := alpha) (u0 := u0) (u1 := u1)
    (S := S) (Aset := Aset) (Owner := Owner)
    W R G A B hzero hone hsigma hfixed w (hTgood hw) (hTG w hw)
  simpa only [fullOwnerError6401] using
    (twoRowPolynomialGauge_errorInterpolant_map_eq_self6401
      (sigma := sigma) (alpha := alpha) (u0 := u0) (u1 := u1)
      (S := S) (Aset := Aset) (Owner := Owner)
      W A B K w hfixed hcop hfailure hgauge)
end SourceAdapters
end BCHKSExtremePrimitiveTerminalPolynomialGaugeSourceAdapters6401
end ProximityPrize.SubmissionLower

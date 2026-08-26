import ProximityPrize.SubmissionLower.BCHKSExtremePrimitivePunctureDerivativeRecovery6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitivePolynomialGaugeFullTail6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTerminalPunctureDerivativeIntegration6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
open BCHKSExtremePrimitivePolynomialGaugeFullTail6401
open BCHKSExtremePrimitivePunctureDerivativeRecovery6401
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000
section AbstractDerivativeSlope
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem fixedDirectionDerivative_eq_of_heavyAgreement6401
    (sigma : F →+* F) (beta : F) (hbeta : sigma beta = beta)
    (L K V0 V1 : F[X]) (Owner E : F → F[X])
    (u0 u1 : F) (T : Finset F)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (hlarge : q6401 < T.card)
    (hLzero : L.eval beta = 0)
    (hEfixed : ∀ z ∈ T, (E z).map sigma = E z)
    (hidentity : ∀ z ∈ T,
      L * K * Owner z = V0 + Polynomial.C z * V1 + E z)
    (hagreement : ∀ z ∈ T,
      (Owner z).eval beta = u0 + z * u1) :
    V1.derivative.eval beta =
      L.derivative.eval beta * K.eval beta * u1 := by
  let a : F := L.derivative.eval beta * K.eval beta * u0 -
    V0.derivative.eval beta
  let b : F := L.derivative.eval beta * K.eval beta * u1 -
    V1.derivative.eval beta
  have hfixedValues : ∀ z ∈ T,
      sigma (a + z * b) = a + z * b := by
    intro z hz
    have hderivative := fixedErrorDerivative_affine_at_simpleRoot6401
      L K V0 V1 Owner E u0 u1 beta T hLzero hidentity hagreement z hz
    have hfixedDerivative := derivative_eval_fixed_of_map_eq_self6401
      sigma beta hbeta (E z) (hEfixed z hz)
    change (E z).derivative.eval beta = a + z * b at hderivative
    rw [← hderivative]
    exact hfixedDerivative
  have hb : b = 0 :=
    fixedAffineValues_many_forces_slope_zero6401
      sigma T a b hfixedCard hlarge hfixedValues
  dsimp only [b] at hb
  linear_combination -hb
end AbstractDerivativeSlope
section CanonicalGaugeInterpolants
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
noncomputable def twoRowPolynomialGaugeReceivedZero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (K : F[X]) : F[X] :=
  fullWordInterpolant6401 alpha (fun i ↦
    (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) * u0 i)
noncomputable def twoRowPolynomialGaugeReceivedOne6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (K : F[X]) : F[X] :=
  fullWordInterpolant6401 alpha (fun i ↦
    (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) * u1 i)
noncomputable def twoRowPolynomialGaugeErrorInterpolant6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (K : F[X]) (z : F) : F[X] :=
  fullWordInterpolant6401 alpha (fun i ↦
    (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
      fullOwnerError6401 W z i)
theorem twoRowPolynomialGauge_reconstructionIdentity6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (K : F[X]) (z : F)
    (hdegree :
      ((twoRowSourcePunctureLocator6401 W * K) * Owner z).natDegree <
        n6401) :
    (twoRowSourcePunctureLocator6401 W * K) * Owner z =
    fullWordInterpolant6401 alpha (fun i ↦
        (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) * u0 i) +
      Polynomial.C z * fullWordInterpolant6401 alpha (fun i ↦
        (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) * u1 i) +
      fullWordInterpolant6401 alpha (fun i ↦
        (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
          ((Owner z).eval (alpha i) - (u0 i + z * u1 i))) := by
  exact scaledOwner_eq_receivedLine_add_errorInterpolant6401
    alpha (twoRowSourcePunctureLocator6401 W * K) (Owner z)
      u0 u1 z (by native_decide) hdegree
theorem exists_twoRowPolynomialGauge_receivedOneQuotient6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (K : F[X]) :
    ∃ Q1 : F[X],
      twoRowPolynomialGaugeReceivedOne6401 W K =
        twoRowSourcePunctureLocator6401 W * Q1 := by
  apply twoRowSourcePunctureLocator_dvd_of_eval_zero6401
  intro i hi
  rw [twoRowPolynomialGaugeReceivedOne6401,
    fullWordInterpolant_eval6401, Polynomial.eval_mul,
    twoRowSourcePunctureLocator_eval_eq_zero6401 W i hi]
  simp
end CanonicalGaugeInterpolants
section TerminalLowLoadDeletion
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
noncomputable def terminalOwnersAfterLowLoadPuncture6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (T : Finset F) : Finset F :=
  ownersAfterLowLoadPunctureDeletion6401 T Aset
    (twoRowSourceBadCoordinates6401 W) q6401
theorem terminalOwnersAfterLowLoadPuncture_subset6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (T : Finset F) :
    terminalOwnersAfterLowLoadPuncture6401 W T ⊆ T := by
  exact Finset.sdiff_subset
theorem terminalPunctureDerivativeDeletion_ledger6401 :
    22507 * q6401 = 47955809687531 ∧
      primitiveLaneFactorDescentGoodFloor6401 = 273495283461914576 ∧
      primitiveLaneFactorDescentExceptionCap6401 = 47957940448246 ∧
      primitiveLaneFactorDescentGoodFloor6401 -
          primitiveLaneFactorDescentExceptionCap6401 =
        273447325521466330 ∧
      273447325521466330 - 22507 * q6401 =
        273399369711778799 := by
  native_decide
theorem terminalOwnersAfterLowLoadPuncture_card_ge6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X]) (T : Finset F)
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C) :
    T.card - 47955809687531 ≤
      (terminalOwnersAfterLowLoadPuncture6401 W T).card := by
  have hbad := twoRowSourceBadCoordinates_card_le_22507_of_terminalLanes6401
    W R G A B hG hA hB hzero hone
  have hgeneric := ownersAfterLowLoadPunctureDeletion_card_ge6401
    T Aset (twoRowSourceBadCoordinates6401 W) q6401
  have hcost :
      (twoRowSourceBadCoordinates6401 W).card * q6401 ≤
        47955809687531 := by
    calc
      (twoRowSourceBadCoordinates6401 W).card * q6401 ≤
          22507 * q6401 := Nat.mul_le_mul_right q6401 hbad
      _ = 47955809687531 := terminalPunctureDerivativeDeletion_ledger6401.1
  change T.card -
      (twoRowSourceBadCoordinates6401 W).card * q6401 ≤
        (terminalOwnersAfterLowLoadPuncture6401 W T).card at hgeneric
  omega
theorem terminalOwnersAfterLowLoadPuncture_card_ge_floor6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X]) (T : Finset F)
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hTcard : primitiveLaneFactorDescentGoodFloor6401 -
      primitiveLaneFactorDescentExceptionCap6401 ≤ T.card) :
    273399369711778799 ≤
      (terminalOwnersAfterLowLoadPuncture6401 W T).card := by
  have hretained := terminalOwnersAfterLowLoadPuncture_card_ge6401
    W R G A B T hG hA hB hzero hone
  have hpre := terminalPunctureDerivativeDeletion_ledger6401.2.2.2.1
  have hpost := terminalPunctureDerivativeDeletion_ledger6401.2.2.2.2
  omega
theorem terminalSurvivor_badAgreement_has_heavyFibre6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (T : Finset F) (z : F)
    (hz : z ∈ terminalOwnersAfterLowLoadPuncture6401 W T)
    (i : Fin n6401)
    (hiBad : i ∈ twoRowSourceBadCoordinates6401 W)
    (hiz : i ∈ Aset z) :
    q6401 < (agreementOwnerFibre6401 T Aset i).card := by
  exact surviving_punctureAgreement_has_heavyFibre6401
    T Aset (twoRowSourceBadCoordinates6401 W) q6401 z hz i hiBad hiz
end TerminalLowLoadDeletion
section TerminalDerivativeSourceAPI
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem terminalSurvivor_badAgreement_derivativeSlope_of_data6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (T : Finset F) (K V0 V1 : F[X]) (E : F → F[X])
    (z : F) (hz : z ∈ terminalOwnersAfterLowLoadPuncture6401 W T)
    (i : Fin n6401)
    (hiBad : i ∈ twoRowSourceBadCoordinates6401 W)
    (hiz : i ∈ Aset z)
    (hfixed : sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (hKpoint : K.eval (alpha i) ≠ 0)
    (hEfixed : ∀ w ∈ agreementOwnerFibre6401 T Aset i,
      (E w).map sigma = E w)
    (hidentity : ∀ w ∈ agreementOwnerFibre6401 T Aset i,
      twoRowSourcePunctureLocator6401 W * K * Owner w =
        V0 + Polynomial.C w * V1 + E w)
    (hAgreement : ∀ w ∈ agreementOwnerFibre6401 T Aset i,
      (Owner w).eval (alpha i) = u0 i + w * u1 i) :
    q6401 < (agreementOwnerFibre6401 T Aset i).card ∧
      K.eval (alpha i) ≠ 0 ∧
      V1.derivative.eval (alpha i) =
        (twoRowSourcePunctureLocator6401 W).derivative.eval (alpha i) *
          K.eval (alpha i) * u1 i := by
  have hheavy := terminalSurvivor_badAgreement_has_heavyFibre6401
    W T z hz i hiBad hiz
  refine ⟨hheavy, hKpoint, ?_⟩
  apply fixedDirectionDerivative_eq_of_heavyAgreement6401
    sigma (alpha i) hfixed
      (twoRowSourcePunctureLocator6401 W) K V0 V1 Owner E
      (u0 i) (u1 i) (agreementOwnerFibre6401 T Aset i)
      hfixedCard hheavy
      (twoRowSourcePunctureLocator_eval_eq_zero6401 W i hiBad)
      hEfixed hidentity
  exact hAgreement
theorem terminalSurvivor_badAgreement_recoversQuotient_of_data6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (T : Finset F) (K V0 V1 Q1 : F[X]) (E : F → F[X])
    (z : F) (hz : z ∈ terminalOwnersAfterLowLoadPuncture6401 W T)
    (i : Fin n6401)
    (hiBad : i ∈ twoRowSourceBadCoordinates6401 W)
    (hiz : i ∈ Aset z)
    (hfixed : sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (hKpoint : K.eval (alpha i) ≠ 0)
    (hEfixed : ∀ w ∈ agreementOwnerFibre6401 T Aset i,
      (E w).map sigma = E w)
    (hidentity : ∀ w ∈ agreementOwnerFibre6401 T Aset i,
      twoRowSourcePunctureLocator6401 W * K * Owner w =
        V0 + Polynomial.C w * V1 + E w)
    (hAgreement : ∀ w ∈ agreementOwnerFibre6401 T Aset i,
      (Owner w).eval (alpha i) = u0 i + w * u1 i)
    (hV1 : V1 = twoRowSourcePunctureLocator6401 W * Q1) :
    q6401 < (agreementOwnerFibre6401 T Aset i).card ∧
      K.eval (alpha i) ≠ 0 ∧
      Q1.eval (alpha i) = K.eval (alpha i) * u1 i := by
  have hslope := terminalSurvivor_badAgreement_derivativeSlope_of_data6401
    W T K V0 V1 E z hz i hiBad hiz hfixed hfixedCard hKpoint
      hEfixed hidentity hAgreement
  refine ⟨hslope.1, hslope.2.1, ?_⟩
  have hLzero := twoRowSourcePunctureLocator_eval_eq_zero6401 W i hiBad
  have hLderivative :=
    twoRowSourcePunctureLocator_derivative_eval_ne_zero6401 W i hiBad
  have hproductDerivative :
      V1.derivative.eval (alpha i) =
        (twoRowSourcePunctureLocator6401 W).derivative.eval (alpha i) *
          Q1.eval (alpha i) := by
    rw [hV1, Polynomial.derivative_mul]
    simp [hLzero]
  have hmul :
      (twoRowSourcePunctureLocator6401 W).derivative.eval (alpha i) *
          Q1.eval (alpha i) =
        (twoRowSourcePunctureLocator6401 W).derivative.eval (alpha i) *
          (K.eval (alpha i) * u1 i) := by
    rw [← hproductDerivative]
    simpa [mul_assoc] using hslope.2.2
  exact mul_left_cancel₀ hLderivative hmul
end TerminalDerivativeSourceAPI
end BCHKSExtremePrimitiveTerminalPunctureDerivativeIntegration6401
end ProximityPrize.SubmissionLower

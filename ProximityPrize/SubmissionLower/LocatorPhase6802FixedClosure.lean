import ProximityPrize.SubmissionLower.LocatorPhase6802Bridge
import ProximityPrize.SubmissionLower.LocatorPhase6802Certificate

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Composition

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180
  RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN319
open LocatorSelection6802 LocatorFactorAggregate LocatorBatchPhase6802
  LocatorPhase6802Oracle LocatorPhase6802Audit LocatorPhase6802Kernels
  LocatorPhase6802SourceSound LocatorPhase6802Bridge LocatorFixedBridge6802

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

/-- End-to-end fixed-part theorem.  Once the generated receipt constructs a
`PhasePrefixCertificate`, no algebraic or combinatorial premises remain. -/
theorem gcd_fixed_count_le_of_certificate
    (cert : PhasePrefixCertificate)
    (u0 u1 : I → K) (S : LocatorSelection6802.SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771) :
    (LocatorCover.fixed
      (fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer6802.initialRegularCap +
        LocatorArithmetic6802.fixedSingularCap := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := LocatorCover.fixed phi Gamma S.QA S.QB
  let U := LocatorFixedBridge6802.initialAUniversalFactors u0 u1 H
  have hH : H ≠ 0 := by
    simpa only [H, gcd12] using gcd_ne_zero_of_left S.QA_ne
  have hsub : Delta ⊆ Gamma := by
    intro gamma hgamma
    have hm : gamma ∈ Gamma ∧
        phi gamma (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, LocatorCover.fixed, Finset.mem_filter] using hgamma
    exact hm.1
  have hdegreeD : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
  have hagreementD : ∀ gamma ∈ Delta, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hsub hgamma)
  have hnoD : NoLargeSelectedPencil selected Delta 131071 80771 :=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80771 hsub hno
  have hown : ∀ F ∈ U, LocatorHybridCostC2.OwnBoundC2
      (regularSeeds H selected Delta F).card
      (regularCumulativeFlag H F) := by
    intro F hFU
    exact LocatorFixedBridge6802.initialA_universal_ownBound u0 u1 H hH S.common_total_le
      selected Delta hdegreeD hagreementD hnoD F hFU
  have hphase := cert.stateLocalBoundOn u0 u1 H selected Delta U
    hdegreeD hagreementD hnoD hown
  apply LocatorPhase6802Bridge.gcd_fixed_count_le_of_stateLocalPhase u0 u1 S selected Gamma
    hdegree hagreement hno
    (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix
      cert.s390Prefix)
  · simpa only [H, phi, Delta, U] using hphase
  · intro p hr hs hy ht
    simpa only [LocatorFixedBridge6802.initialAHelperCap] using
      LocatorInitialA6802.initialAHelperCap_le_potential p hr hs hy ht
  · exact cert.joint

end

end ProximityPrize.SubmissionLower.LocatorPhase6802Composition

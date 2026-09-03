import ProximityPrize.SubmissionLower.LocatorProtocol6802

namespace ProximityPrize.SubmissionLower.LocatorClosure6802

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN319 RCN238 RCN259 RCN156 RCN234 LocatorSelection6802

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

abbrev K := LocatorPhase6802Composition.K
abbrev I := LocatorPhase6802Composition.I
abbrev P4 := LocatorPhase6802Composition.P4

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem selected_pair_count_of_certificate
    (cert : LocatorPhase6802Composition.PhasePrefixCertificate)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ seeds, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds 131071 80771) :
    seeds.card < LocatorArithmetic6802.budget := by
  have hnoResidual : NoLargeSelectedPencil selected seeds LocatorArithmetic6802.w
      (LocatorArithmetic6802.n - LocatorArithmetic6802.agreements) := by
    simpa only [LocatorArithmetic6802.w, LocatorArithmetic6802.n,
      LocatorArithmetic6802.agreements, Nat.reduceSub] using hno
  let phi : K → P4 →+* Polynomial K := fun gamma ↦
    (specialization K (selected gamma) gamma).toRingHom
  have hparents (gamma : K) (hg : gamma ∈ seeds) :
      specialization K (selected gamma) gamma S.QA = 0 ∧
      specialization K (selected gamma) gamma S.QB = 0 := by
    exact S.universal_vanishing gamma (selected gamma)
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
      (hdegree gamma hg) (hagreement gamma hg)
      (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
  have hnodes : (Finset.univ : Finset I).card = LocatorArithmetic6802.n := by
    norm_num [I, IRSProfile.Index, LocatorArithmetic6802.n]
  have hfixedRaw :=
    LocatorPhase6802Composition.gcd_fixed_count_le_of_certificate cert
      u0 u1 S selected seeds hdegree hagreement hno
  have hfixed : (LocatorCover.fixed phi seeds S.QA S.QB).card ≤
      257422060420373924 + LocatorArithmetic6802.fixedSingularCap := by
    simpa only [phi, K, P4, LocatorPhase6802Composition.K,
      LocatorPhase6802Composition.P4, LocatorSelection6802.K, LocatorSelection6802.P4,
      LocatorFixedConsumer6802.initialRegularCap, LocatorArithmetic6802.fixedRegularCap]
      using hfixedRaw
  have hresidualRaw := LocatorResidual6802.gcd_residual_count_lt (K := K) (I := I)
    S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag
    selected seeds (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hnodes hdegree
    (fun gamma hg ↦ (hparents gamma hg).1)
    (fun gamma hg ↦ (hparents gamma hg).2) hagreement hnoResidual
  have hresidual : (LocatorCover.residual phi seeds S.QA S.QB).card <
      LocatorArithmetic6802.residualStage.regularCountCap +
        (LocatorArithmetic6802.sB - 1) * LocatorArithmetic6802.chainStage.regularCountCap +
        (LocatorArithmetic6802.sB + 1) * LocatorArithmetic6802.tailSingular.countCap + 1 := by
    simpa only [phi, K, P4, LocatorPhase6802Composition.K,
      LocatorPhase6802Composition.P4, LocatorSelection6802.K, LocatorSelection6802.P4]
      using hresidualRaw
  have hpartition := LocatorCover.partition_card phi seeds S.QA S.QB
  have hledger := LocatorArithmetic6802.ledger_lt
  unfold LocatorArithmetic6802.ledger LocatorArithmetic6802.fixedRegularCap at hledger
  simp only [LocatorArithmetic6802.sB, Nat.reduceSub, Nat.reduceAdd] at hresidual hledger
  omega

theorem selectedNoLargePencilBound6802_of_certificate
    (cert : LocatorPhase6802Composition.PhasePrefixCertificate) :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80771
      LocatorArithmetic6802.budget := by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hA : ∀ gamma ∈ seeds, 181373 ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcard gamma hg
    simpa [I, IRSProfile.Index] using hc
  have hagreement : ∀ gamma ∈ seeds, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds 131071 80771 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt
    (selected_pair_count_of_certificate cert (U 0) (U 1) S selected seeds
      hdegree hagreement hno')

theorem alignmentBound6802_of_certificate
    (cert : LocatorPhase6802Composition.PhasePrefixCertificate) :
    AffineLineAlignmentBound IRSProfile.baseCode
      LocatorProtocol6802.errors LocatorProtocol6802.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80771
    LocatorArithmetic6802.budget
    (selectedNoLargePencilBound6802_of_certificate cert)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
    LocatorArithmetic6802.budget, LocatorProtocol6802.errors,
    LocatorProtocol6802.mcaBudget] using h

theorem protocolClaim6802_of_certificate
    (cert : LocatorPhase6802Composition.PhasePrefixCertificate) :
    ProtocolClaim 6802 10338815 33554432 :=
  LocatorProtocol6802.protocolClaim6802_of_alignment
    (alignmentBound6802_of_certificate cert)

/-- The non-parameterized benchmark claim obtained from the checked receipt. -/
theorem protocolClaim6802 : ProtocolClaim 6802 10338815 33554432 :=
  protocolClaim6802_of_certificate LocatorPhase6802Certificate.certificate

end

end ProximityPrize.SubmissionLower.LocatorClosure6802

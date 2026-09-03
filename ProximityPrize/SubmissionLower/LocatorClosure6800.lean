import ProximityPrize.SubmissionLower.LocatorPhase6800Composition
import ProximityPrize.SubmissionLower.LocatorPhase6800Certificate
import ProximityPrize.SubmissionLower.LocatorResidual
import ProximityPrize.SubmissionLower.LocatorProtocol

/-!
# Final reduction closure for the 6800 certificate

This module keeps the protocol and residual argument independent of the
generated receipt representation.  The only input is the sound
`PhasePrefixCertificate` exported by the phase composition layer.
-/

namespace ProximityPrize.SubmissionLower.LocatorClosure6800

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN319 RCN238 RCN259 RCN156 RCN234 LocatorSelection

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

abbrev K := LocatorPhase6800Composition.K
abbrev I := LocatorPhase6800Composition.I
abbrev P4 := LocatorPhase6800Composition.P4

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem selected_pair_count_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ seeds, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds 131071 80752) :
    seeds.card < LocatorArithmetic.budget := by
  have hnoResidual : NoLargeSelectedPencil selected seeds LocatorArithmetic.w
      (LocatorArithmetic.n - LocatorArithmetic.agreements) := by
    simpa only [LocatorArithmetic.w, LocatorArithmetic.n,
      LocatorArithmetic.agreements, Nat.reduceSub] using hno
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
  have hnodes : (Finset.univ : Finset I).card = LocatorArithmetic.n := by
    norm_num [I, IRSProfile.Index, LocatorArithmetic.n]
  have hfixedRaw :=
    LocatorPhase6800Composition.gcd_fixed_count_le_of_certificate cert
      u0 u1 S selected seeds hdegree hagreement hno
  have hfixed : (LocatorCover.fixed phi seeds S.QA S.QB).card ≤
      259787835303351020 + LocatorArithmetic.fixedSingularCap := by
    simpa only [phi, K, P4, LocatorPhase6800Composition.K,
      LocatorPhase6800Composition.P4, LocatorSelection.K, LocatorSelection.P4,
      LocatorFixedConsumer.initialRegularCap, LocatorArithmetic.fixedRegularCap]
      using hfixedRaw
  have hresidualRaw := LocatorResidual.gcd_residual_count_lt (K := K) (I := I)
    S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag
    selected seeds (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hnodes hdegree
    (fun gamma hg ↦ (hparents gamma hg).1)
    (fun gamma hg ↦ (hparents gamma hg).2) hagreement hnoResidual
  have hresidual : (LocatorCover.residual phi seeds S.QA S.QB).card <
      LocatorArithmetic.residualStage.regularCountCap +
        (LocatorArithmetic.sB - 1) * LocatorArithmetic.chainStage.regularCountCap +
        (LocatorArithmetic.sB + 1) * LocatorArithmetic.tailSingular.countCap + 1 := by
    simpa only [phi, K, P4, LocatorPhase6800Composition.K,
      LocatorPhase6800Composition.P4, LocatorSelection.K, LocatorSelection.P4]
      using hresidualRaw
  have hpartition := LocatorCover.partition_card phi seeds S.QA S.QB
  have hledger := LocatorArithmetic.ledger_lt
  unfold LocatorArithmetic.ledger LocatorArithmetic.fixedRegularCap at hledger
  simp only [LocatorArithmetic.sB, Nat.reduceSub, Nat.reduceAdd] at hresidual hledger
  omega

theorem selectedNoLargePencilBound6800_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate) :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80752
      LocatorArithmetic.budget := by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hA : ∀ gamma ∈ seeds, 181392 ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcard gamma hg
    simpa [I, IRSProfile.Index] using hc
  have hagreement : ∀ gamma ∈ seeds, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds 131071 80752 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt
    (selected_pair_count_of_certificate cert (U 0) (U 1) S selected seeds
      hdegree hagreement hno')

theorem alignmentBound6800_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate) :
    AffineLineAlignmentBound IRSProfile.baseCode
      LocatorProtocol.errors LocatorProtocol.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80752
    LocatorArithmetic.budget
    (selectedNoLargePencilBound6800_of_certificate cert)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
    LocatorArithmetic.budget, LocatorProtocol.errors,
    LocatorProtocol.mcaBudget] using h

theorem protocolClaim6800_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate) :
    ProtocolClaim 6800 10336383 33554432 :=
  LocatorProtocol.protocolClaim6800_of_alignment
    (alignmentBound6800_of_certificate cert)

/-- The non-parameterized benchmark claim obtained from the checked receipt. -/
theorem protocolClaim6800 : ProtocolClaim 6800 10336383 33554432 :=
  protocolClaim6800_of_certificate LocatorPhase6800Certificate.certificate

end

end ProximityPrize.SubmissionLower.LocatorClosure6800

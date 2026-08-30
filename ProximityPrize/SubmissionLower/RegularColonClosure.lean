import ProximityPrize.SubmissionLower.RegularColonFixedBridge
import ProximityPrize.SubmissionLower.RegularColonResidual
import ProximityPrize.SubmissionLower.RegularColonProtocol
import ProximityPrize.SubmissionLower.DV

/- Proposed unconditional entry. Compilation and kernel checking are deferred
   to the authorized remote verifier. No counting hypothesis is exported. -/
namespace ProximityPrize.SubmissionLower.RegularColonClosure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN319 RCN238
open RCN259 RCN156
open RCN234
open TwoKernelSelection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem selected_pair_count
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ seeds, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds 131071 80112) :
    seeds.card < RegularColonArithmetic.budget := by
  let phi := fun gamma => (specialization K (selected gamma) gamma).toRingHom
  have hparents (gamma : K) (hg : gamma ∈ seeds) :
      specialization K (selected gamma) gamma S.QA = 0 ∧
      specialization K (selected gamma) gamma S.QB = 0 := by
    exact S.universal_vanishing gamma (selected gamma)
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i))
      (hdegree gamma hg) (hagreement gamma hg)
      (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hcap := TwoKernelCaps.SelectedPair.common_caps S
  have hnodes : (Finset.univ : Finset I).card = RegularColonArithmetic.n := by
    norm_num [I, IRSProfile.Index, RegularColonArithmetic.n]
  apply TwoInterpolatorCover.count_lt_budget phi seeds S.QA S.QB
    (wt residualTotalWeights (gcd12 S.QA S.QB)) hcap.2
  · intro hlow
    constructor
    · exact RegularColonFixedBridge.gcd_fixed_count_le 1280 (Or.inl rfl)
        u0 u1 S hlow selected seeds hdegree hagreement hno
    · exact RegularColonResidual.gcd_residual_count_lt 0 (Or.inl rfl)
        S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag (Nat.zero_le _)
        selected seeds (Finset.univ : Finset I) IRSProfile.domain u0 u1
        IRSProfile.domain.injective.injOn hnodes hdegree
        (fun gamma hg => (hparents gamma hg).1)
        (fun gamma hg => (hparents gamma hg).2) hagreement hno
  · intro hhigh hmax
    constructor
    · exact RegularColonFixedBridge.gcd_fixed_count_le 1282 (Or.inr rfl)
        u0 u1 S hmax selected seeds hdegree hagreement hno
    · exact RegularColonResidual.gcd_residual_count_lt 1281 (Or.inr rfl)
        S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag hhigh
        selected seeds (Finset.univ : Finset I) IRSProfile.domain u0 u1
        IRSProfile.domain.injective.injOn hnodes hdegree
        (fun gamma hg => (hparents gamma hg).1)
        (fun gamma hg => (hparents gamma hg).2) hagreement hno

theorem selectedNoLargePencilBound6735 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80112
      RegularColonArithmetic.budget := by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hA : ∀ gamma ∈ seeds, 182032 ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcard gamma hg
    simpa [I, IRSProfile.Index] using hc
  have hagreement : ∀ gamma ∈ seeds, 182032 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds 131071 80112 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt (selected_pair_count (U 0) (U 1) S selected seeds
    hdegree hagreement hno')

theorem alignmentBound6735 :
    AffineLineAlignmentBound IRSProfile.baseCode
      RegularColonProtocol.errors RegularColonProtocol.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80112
    RegularColonArithmetic.budget selectedNoLargePencilBound6735
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
    RegularColonArithmetic.budget, RegularColonProtocol.errors,
    RegularColonProtocol.mcaBudget] using h

theorem protocolClaim6735 : ProtocolClaim 6735 10254463 33554432 :=
  RegularColonProtocol.protocolClaim6735_of_alignment alignmentBound6735

end
end ProximityPrize.SubmissionLower.RegularColonClosure

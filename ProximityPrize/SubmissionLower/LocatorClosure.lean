import ProximityPrize.SubmissionLower.LocatorFixedBridge
import ProximityPrize.SubmissionLower.LocatorResidual
import ProximityPrize.SubmissionLower.LocatorProtocol
import ProximityPrize.SubmissionLower.DV

/- Unconditional 67.43 candidate: every counting premise is supplied by
   the span-selected pair, whole-kernel divisor bounds and stage theorems. -/
namespace ProximityPrize.SubmissionLower.LocatorClosure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN319 RCN238 RCN259 RCN156 RCN234
open LocatorSelection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem selected_pair_count
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ seeds, 181943 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds 131071 80201) :
    seeds.card < LocatorArithmetic.budget := by
  have hnoResidual : NoLargeSelectedPencil selected seeds LocatorArithmetic.w
      (LocatorArithmetic.n - LocatorArithmetic.agreements) := by
    simpa only [LocatorArithmetic.w, LocatorArithmetic.n,
      LocatorArithmetic.agreements, Nat.reduceSub] using hno
  let phi := fun gamma => (specialization K (selected gamma) gamma).toRingHom
  have hparents (gamma : K) (hg : gamma ∈ seeds) :
      specialization K (selected gamma) gamma S.QA = 0 ∧
      specialization K (selected gamma) gamma S.QB = 0 := by
    exact S.universal_vanishing gamma (selected gamma)
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i))
      (hdegree gamma hg) (hagreement gamma hg)
      (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hnodes : (Finset.univ : Finset I).card = LocatorArithmetic.n := by
    norm_num [I, IRSProfile.Index, LocatorArithmetic.n]
  have hfixed := LocatorFixedBridge.gcd_fixed_count_le u0 u1 S
    selected seeds hdegree hagreement hno
  have hresidual := LocatorResidual.gcd_residual_count_lt
    S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag
    selected seeds (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hnodes hdegree
    (fun gamma hg => (hparents gamma hg).1)
    (fun gamma hg => (hparents gamma hg).2) hagreement hnoResidual
  have hpartition := LocatorCover.partition_card phi seeds S.QA S.QB
  dsimp only [phi] at hpartition
  have hledger := LocatorArithmetic.ledger_lt
  unfold LocatorArithmetic.ledger LocatorArithmetic.fixedRegularCap at hledger
  omega

theorem selectedNoLargePencilBound6744 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80201
      LocatorArithmetic.budget := by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hA : ∀ gamma ∈ seeds, 181943 ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcard gamma hg
    simpa [I, IRSProfile.Index] using hc
  have hagreement : ∀ gamma ∈ seeds, 181943 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds 131071 80201 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt (selected_pair_count (U 0) (U 1) S selected seeds
    hdegree hagreement hno')

theorem alignmentBound6744 :
    AffineLineAlignmentBound IRSProfile.baseCode
      LocatorProtocol.errors LocatorProtocol.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80201
    LocatorArithmetic.budget selectedNoLargePencilBound6744
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
    LocatorArithmetic.budget, LocatorProtocol.errors,
    LocatorProtocol.mcaBudget] using h

theorem protocolClaim6744 : ProtocolClaim 6744 10265855 33554432 :=
  LocatorProtocol.protocolClaim6744_of_alignment alignmentBound6744

end
end ProximityPrize.SubmissionLower.LocatorClosure

import ProximityPrize.SubmissionLower.LocatorSelection6803
import ProximityPrize.SubmissionLower.LocatorProtocol6803

/-!
# Protocol closure scaffold for 68.03

This file isolates the routine outer reduction from the correlated locator
count.  The final geometric assembly only has to inhabit `SelectedPairCountBound`;
the affine-line alignment and protocol claim then follow here.
-/

namespace ProximityPrize.SubmissionLower.LocatorClosureScaffold6803

open ProximityPrize.Benchmark
open scoped Classical
open RCN050 RCN156 RCN234 RCN238 RCN259 RCN319
open LocatorSelection6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

abbrev K := LocatorSelection6803.K
abbrev I := LocatorSelection6803.I

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

/-- The sole inner combinatorial obligation left to the correlated locator
assembly. -/
def SelectedPairCountBound : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K),
    (∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071) →
    (∀ gamma ∈ seeds, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected seeds 131071 80781 →
    seeds.card < LocatorProtocol6803.mcaBudget

theorem selectedNoLargePencilBound_of_pair_count
    (hcount : SelectedPairCountBound) :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80781
      LocatorProtocol6803.mcaBudget := by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hA : ∀ gamma ∈ seeds, 181363 ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcard gamma hg
    simpa [I, IRSProfile.Index] using hc
  have hagreement : ∀ gamma ∈ seeds, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds 131071 80781 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt
    (hcount (U 0) (U 1) S selected seeds hdegree hagreement hno')

theorem alignmentBound_of_pair_count (hcount : SelectedPairCountBound) :
    AffineLineAlignmentBound IRSProfile.baseCode
      LocatorProtocol6803.errors LocatorProtocol6803.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80781
    LocatorProtocol6803.mcaBudget
    (selectedNoLargePencilBound_of_pair_count hcount)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
    LocatorProtocol6803.errors, LocatorProtocol6803.mcaBudget] using h

theorem protocolClaim6803_of_pair_count (hcount : SelectedPairCountBound) :
    ProtocolClaim 6803 10340095 33554432 :=
  LocatorProtocol6803.protocolClaim6803_of_alignment
    (alignmentBound_of_pair_count hcount)

end

end ProximityPrize.SubmissionLower.LocatorClosureScaffold6803

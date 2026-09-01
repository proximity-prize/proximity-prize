import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ContactTranslation6600Research
namespace ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research
open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactInterpolation ContactTranslation
open ContactTranslation6600Research ContactPrimeSeedIncidence
open ContactParameters6600Research
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
def SelectedNoLargePencilBound6600:Prop:=
  SelectedNoLargePencilBound IRSProfile.domain w errors alignmentBudget
def GlobalCountLtAlignment6600:Prop:=
  ∀ (Q:MvPolynomial (Fin 4) IRSProfile.Field),
    Q≠0 →
    Q∈globalCoefficientBox IRSProfile.Field
      weightedCap w seedTotalCap slopeCap →
    ∀ (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
      (seeds:Finset IRSProfile.Field)
      (u0 u1:IRSProfile.Index → IRSProfile.Field),
      (∀ gamma∈seeds,(selected gamma).natDegree ≤ w) →
      (∀ gamma∈seeds,
        specialization IRSProfile.Field (selected gamma) gamma Q=0) →
      (∀ gamma∈seeds,agreements ≤
        (Finset.univ.filter (fun i:IRSProfile.Index↦
          (selected gamma).eval (IRSProfile.domain i)=
            u0 i+gamma*u1 i)).card) →
      NoLargeSelectedPencil selected seeds w errors →
      seeds.card < alignmentBudget
abbrev InterpolantSelectedCount6600:=GlobalCountLtAlignment6600
theorem challenge_field_characteristic6600:
    CharP IRSProfile.Field prime:=by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem original_support_card6600
    (A:IRSProfile.Field → Finset IRSProfile.Index)
    (seeds:Finset IRSProfile.Field)
    (hcard:∀ gamma∈seeds,
      Fintype.card IRSProfile.Index-errors ≤ (A gamma).card):
    ∀ gamma∈seeds,agreements ≤ (A gamma).card:=by
  intro gamma hgamma
  have h:=hcard gamma hgamma
  simpa [IRSProfile.Index,agreements,n,errors] using h
theorem selected_count_of_global_count_lt_alignment6600
    (hcount:GlobalCountLtAlignment6600):
    SelectedNoLargePencilBound6600:=by
  classical
  intro U seeds A selected hdegree hcard hvalues hno
  have hcard':=original_support_card6600 A seeds hcard
  obtain ⟨Q,hQ,hbox,hvanish⟩:=
    exists_frozen_universal_vanishing_interpolant6600 (U 0) (U 1)
  have hsolution:∀ gamma∈seeds,
      specialization IRSProfile.Field (selected gamma) gamma Q=0:=by
    intro gamma hgamma
    exact hvanish gamma (selected gamma) (A gamma)
      (hdegree gamma hgamma) (hcard' gamma hgamma) (hvalues gamma hgamma)
  have hagreement:∀ gamma∈seeds,agreements ≤
      (Finset.univ.filter (fun i:IRSProfile.Index↦
        (selected gamma).eval (IRSProfile.domain i)=
          U 0 i+gamma*U 1 i)).card:=by
    intro gamma hgamma
    apply le_trans (hcard' gamma hgamma)
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i,hvalues gamma hgamma i hi⟩
  have hno':NoLargeSelectedPencil selected seeds w errors:=by
    intro P0 P1 h0 h1
    have hp:=hno P0 P1 h0 h1
    refine le_trans ?_ hp
    apply Finset.card_le_card
    intro gamma hgamma
    simpa only [pencilSeeds,Finset.mem_filter] using
      (Finset.mem_filter.mp hgamma)
  exact Nat.le_of_lt
    (hcount Q hQ hbox selected seeds (U 0) (U 1)
      hdegree hsolution hagreement hno')
theorem alignment_of_global_count_lt_alignment6600
    (hcount:GlobalCountLtAlignment6600):
    AffineLineAlignmentBound IRSProfile.baseCode errors alignmentBudget:=by
  change AffineLineAlignmentBound
    (ReedSolomon.code IRSProfile.domain (w+1)) errors alignmentBudget
  exact alignmentBound_of_selected_count IRSProfile.domain w errors
    alignmentBudget (selected_count_of_global_count_lt_alignment6600 hcount)
end
end ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research

import ProximityPrize.SubmissionLower.Koala6844VirtualShortAdaptiveExhaustion
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetGap
import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticBundle01
import ProximityPrize.SubmissionLower.Koala6844ReceiptsExactBand


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Koala6844Normalization Koala6844Receipts
open RCN095 RCN130 RCN266 LocatorBatchProductRoute LocatorLowQuotient LocatorFactorAggregate
open Koala6831MovingAdaptive (aggregateFlag)

noncomputable section

set_option autoImplicit false

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
variable {data : CenteredVirtualData x domain σ degree agreements errors excess}

private def centeredAdaptiveSource_of_firstJetReceipt
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (shape : FirstJetShape) (margin : ℕ) (hsize : domain.card ≤ nodes)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hmargin : margin = firstJetGap shape 0)
    (hm : 0 < shape.m) (hBdegree : shape.s < degree) (hBprime : shape.s < prime)
    (hM : shape.m+shape.s ≤ (firstJetFlag shape 0).y)
    (hL : (firstJetFlag shape 0).y ≤ shape.L)
    (hq : shape.q ≤ (firstJetFlag shape 0).y) :
    CenteredAdaptiveSource data prime where
  D := fun _ => firstJetCutoff shape 0
  wQ := degree+poleWidth
  m := shape.m
  L := shape.L
  B := shape.s
  U := (firstJetFlag shape 0).y
  q := shape.q
  gap := margin
  multiplicity_pos := hm
  slope_lt_char := hBprime
  middle_le_total := hL
  lift_le_middle := hq
  cutoff_le_agreement := Nat.sub_le _ _
  middle_le_cutoff := le_rfl
  evaluated_degree := by omega
  dimension := by
    rw [hmargin, firstJetGap_exact shape 0 hBdegree hM hL hq]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hsize) _

def firstCenteredAdaptiveSource
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (hsize : domain.card ≤ nodes)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth) :
    CenteredAdaptiveSource data prime :=
  centeredAdaptiveSource_of_firstJetReceipt data firstAdaptiveShape firstAdaptiveGap hsize hwidth
    firstAdaptive_firstJetGap_eq.symm
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def secondCenteredAdaptiveSource
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (hsize : domain.card ≤ nodes)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth) :
    CenteredAdaptiveSource data prime :=
  centeredAdaptiveSource_of_firstJetReceipt data secondAdaptiveShape secondAdaptiveGap hsize hwidth
    secondAdaptive_firstJetGap_eq.symm
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem firstCenteredAdaptiveSource_numbers
    (hsize : domain.card ≤ nodes)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth) :
    (firstCenteredAdaptiveSource data hsize hwidth).numbers =
      bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap := rfl

theorem secondCenteredAdaptiveSource_numbers
    (hsize : domain.card ≤ nodes)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth) :
    (secondCenteredAdaptiveSource data hsize hwidth).numbers =
      bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap := rfl

theorem exists_two_short_receipt_passes [CharP K prime]
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (hsize : domain.card ≤ nodes)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hfield : A.card < ENat.card K) (hFit : Below (aggregateFlag H A) afterRooms.toFlagDegree)
    (hTrans : ∀ F ∈ A, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    ∃ pass₁ : CenteredAdaptivePass (firstCenteredAdaptiveSource data hsize hwidth) poleWidth H A,
    ∃ pass₂ : CenteredAdaptivePass (secondCenteredAdaptiveSource data hsize hwidth)
      poleWidth H pass₁.residue,
      pass₂.residue = ∅ ∨
        ¬ geometricGate flowWidth (bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap)
          (aggregateFlag H pass₂.residue) ∧
        ¬ geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap)
          (aggregateFlag H pass₂.residue) := by
  let first := firstCenteredAdaptiveSource data hsize hwidth
  let second := secondCenteredAdaptiveSource data hsize hwidth
  have firstEq : first.numbers = bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap :=
    firstCenteredAdaptiveSource_numbers hsize hwidth
  have secondEq : second.numbers = bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap :=
    secondCenteredAdaptiveSource_numbers hsize hwidth
  have fit₁ : AdaptiveSourceFits first.numbers (aggregateFlag H A) := by
    rw [firstEq]
    exact ⟨hFit.1.trans (by decide +kernel), hFit.2.1.trans (by decide +kernel),
      hFit.2.2.trans (by decide +kernel)⟩
  have fit₂ : AdaptiveSourceFits second.numbers (aggregateFlag H A) := by
    rw [secondEq]
    exact ⟨hFit.1.trans (by decide +kernel), hFit.2.1.trans (by decide +kernel),
      hFit.2.2.trans (by decide +kernel)⟩
  obtain ⟨pass₁, pass₂, stop⟩ := exists_two_centered_adaptive_passes first second poleWidth
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hwidth hLead H A hfield fit₁ fit₂ hTrans
  exact ⟨pass₁,pass₂,by simpa only [firstEq,secondEq,flowWidth] using stop⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort


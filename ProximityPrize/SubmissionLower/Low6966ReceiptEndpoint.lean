import ProximityPrize.SubmissionLower.Low6966Tiles0
import ProximityPrize.SubmissionLower.Low6966Tiles1
import ProximityPrize.SubmissionLower.Low6966Tiles2
import ProximityPrize.SubmissionLower.Low6966Tiles3
import ProximityPrize.SubmissionLower.Low6966Tiles4
import ProximityPrize.SubmissionLower.Low6966Tiles5
import ProximityPrize.SubmissionLower.Low6966Tiles6
import ProximityPrize.SubmissionLower.Low6966Tiles7
import ProximityPrize.SubmissionLower.Low6966Tiles8
import ProximityPrize.SubmissionLower.Low6966Tiles9
import ProximityPrize.SubmissionLower.Low6966Tiles10
import ProximityPrize.SubmissionLower.Low6966Tiles11
import ProximityPrize.SubmissionLower.Low6966Tiles12
import ProximityPrize.SubmissionLower.Low6966Tiles13
import ProximityPrize.SubmissionLower.Low6966Tiles14
import ProximityPrize.SubmissionLower.Low6966Tiles15
import ProximityPrize.SubmissionLower.Low6966Tiles16
import ProximityPrize.SubmissionLower.Low6966Tiles17
import ProximityPrize.SubmissionLower.Low6966Tiles18
import ProximityPrize.SubmissionLower.Low6966Tiles19
import ProximityPrize.SubmissionLower.Low6966Tiles20
import ProximityPrize.SubmissionLower.Low6966Tiles21
import ProximityPrize.SubmissionLower.Low6966Tiles22
import ProximityPrize.SubmissionLower.Low6966Tiles23
import ProximityPrize.SubmissionLower.Low6966Tiles24
import ProximityPrize.SubmissionLower.Low6966Tiles25
import ProximityPrize.SubmissionLower.Low6966Tiles26
import ProximityPrize.SubmissionLower.Low6966Tiles27
import ProximityPrize.SubmissionLower.Low6966Tiles28
import ProximityPrize.SubmissionLower.Low6966Tiles29
import ProximityPrize.SubmissionLower.Low6966Tiles30
import ProximityPrize.SubmissionLower.Low6966Tiles31
import ProximityPrize.SubmissionLower.Low6966Tiles32
import ProximityPrize.SubmissionLower.Low6966Tiles33
import ProximityPrize.SubmissionLower.Low6966Gates
import ProximityPrize.SubmissionLower.Low6966CountCore
import ProximityPrize.SubmissionLower.Front6966Rank2
set_option Elab.async false
namespace LowProfile6966
open Low6966Allocation
private def receipts : ∀ k : Band, Receipt k
  | ⟨0,_⟩ => Group0.receipt
  | ⟨1,_⟩ => Group1.receipt
  | ⟨2,_⟩ => Group2.receipt
  | ⟨3,_⟩ => Group3.receipt
  | ⟨4,_⟩ => Group4.receipt
  | ⟨5,_⟩ => Group5.receipt
  | ⟨6,_⟩ => Group6.receipt
  | ⟨7,_⟩ => Group7.receipt
  | ⟨8,_⟩ => Group8.receipt
  | ⟨9,_⟩ => Group9.receipt
  | ⟨10,_⟩ => Group10.receipt
  | ⟨11,_⟩ => Group11.receipt
  | ⟨12,_⟩ => Group12.receipt
  | ⟨13,_⟩ => Group13.receipt
  | ⟨14,_⟩ => Group14.receipt
  | ⟨15,_⟩ => Group15.receipt
  | ⟨16,_⟩ => Group16.receipt
  | ⟨17,_⟩ => Group17.receipt
  | ⟨18,_⟩ => Group18.receipt
  | ⟨19,_⟩ => Group19.receipt
  | ⟨20,_⟩ => Group20.receipt
  | ⟨21,_⟩ => Group21.receipt
  | ⟨22,_⟩ => Group22.receipt
  | ⟨23,_⟩ => Group23.receipt
  | ⟨24,_⟩ => Group24.receipt
  | ⟨25,_⟩ => Group25.receipt
  | ⟨26,_⟩ => Group26.receipt
  | ⟨27,_⟩ => Group27.receipt
  | ⟨28,_⟩ => Group28.receipt
  | ⟨29,_⟩ => Group29.receipt
  | ⟨30,_⟩ => Group30.receipt
  | ⟨31,_⟩ => Group31.receipt
  | ⟨32,_⟩ => Group32.receipt
  | ⟨33,_⟩ => Group33.receipt
  | ⟨k+34,h⟩ => absurd h (by omega)
private theorem receipt_orders : (fun k => (receipts k).orders) = bandOrders :=
  funext fun k => by fin_cases k <;> rfl
theorem low_of_gates (gates : Gates) : Front6966.c6 := by
  obtain ⟨G,bank,table⟩ := gates
  rw [←receipt_orders] at table
  intro _ _ M _ F lo hi
  exact count_with_receipts receipts table bank M F lo hi
#print axioms low_of_gates
end LowProfile6966

import ProximityPrize.SubmissionLower.Low6966Mass0
import ProximityPrize.SubmissionLower.Low6966Mass1
import ProximityPrize.SubmissionLower.Low6966Mass2
import ProximityPrize.SubmissionLower.Low6966Mass3
import ProximityPrize.SubmissionLower.Low6966Mass4
import ProximityPrize.SubmissionLower.Low6966Mass5
import ProximityPrize.SubmissionLower.Low6966Mass6
import ProximityPrize.SubmissionLower.Low6966Mass7
import ProximityPrize.SubmissionLower.Low6966Mass8
import ProximityPrize.SubmissionLower.Low6966Mass9
import ProximityPrize.SubmissionLower.Low6966Mass10
import ProximityPrize.SubmissionLower.Low6966Mass11
import ProximityPrize.SubmissionLower.Low6966Mass12
import ProximityPrize.SubmissionLower.Low6966Mass13
import ProximityPrize.SubmissionLower.Low6966Mass14
import ProximityPrize.SubmissionLower.Low6966Mass15
import ProximityPrize.SubmissionLower.Low6966Mass16
import ProximityPrize.SubmissionLower.Low6966Mass17
import ProximityPrize.SubmissionLower.Low6966Mass18
import ProximityPrize.SubmissionLower.Low6966Mass19
import ProximityPrize.SubmissionLower.Low6966Mass20
import ProximityPrize.SubmissionLower.Low6966Mass21
import ProximityPrize.SubmissionLower.Low6966Mass22
import ProximityPrize.SubmissionLower.Low6966Mass23
import ProximityPrize.SubmissionLower.Low6966Mass24
import ProximityPrize.SubmissionLower.Low6966Mass25
import ProximityPrize.SubmissionLower.Low6966Mass26
import ProximityPrize.SubmissionLower.Low6966Mass27
import ProximityPrize.SubmissionLower.Low6966Mass28
import ProximityPrize.SubmissionLower.Low6966Mass29
import ProximityPrize.SubmissionLower.Low6966Mass30
import ProximityPrize.SubmissionLower.Low6966Mass31
import ProximityPrize.SubmissionLower.Low6966Mass32
import ProximityPrize.SubmissionLower.Low6966Mass33
import ProximityPrize.SubmissionLower.Low6966RetainedCount

set_option Elab.async false
namespace Low6966Allocation
open K1_13 (Shape)
def bandOrders : ∀ k : Band, List (MassCell k)
  | ⟨0,_⟩ => Group0.orders
  | ⟨1,_⟩ => Group1.orders
  | ⟨2,_⟩ => Group2.orders
  | ⟨3,_⟩ => Group3.orders
  | ⟨4,_⟩ => Group4.orders
  | ⟨5,_⟩ => Group5.orders
  | ⟨6,_⟩ => Group6.orders
  | ⟨7,_⟩ => Group7.orders
  | ⟨8,_⟩ => Group8.orders
  | ⟨9,_⟩ => Group9.orders
  | ⟨10,_⟩ => Group10.orders
  | ⟨11,_⟩ => Group11.orders
  | ⟨12,_⟩ => Group12.orders
  | ⟨13,_⟩ => Group13.orders
  | ⟨14,_⟩ => Group14.orders
  | ⟨15,_⟩ => Group15.orders
  | ⟨16,_⟩ => Group16.orders
  | ⟨17,_⟩ => Group17.orders
  | ⟨18,_⟩ => Group18.orders
  | ⟨19,_⟩ => Group19.orders
  | ⟨20,_⟩ => Group20.orders
  | ⟨21,_⟩ => Group21.orders
  | ⟨22,_⟩ => Group22.orders
  | ⟨23,_⟩ => Group23.orders
  | ⟨24,_⟩ => Group24.orders
  | ⟨25,_⟩ => Group25.orders
  | ⟨26,_⟩ => Group26.orders
  | ⟨27,_⟩ => Group27.orders
  | ⟨28,_⟩ => Group28.orders
  | ⟨29,_⟩ => Group29.orders
  | ⟨30,_⟩ => Group30.orders
  | ⟨31,_⟩ => Group31.orders
  | ⟨32,_⟩ => Group32.orders
  | ⟨33,_⟩ => Group33.orders
  | ⟨k+34,h⟩ => absurd h (by omega)
def Gates : Prop := ∃ G : Shape → ℕ, Low6966RetainedCut.GateBank G ∧ GateTable bandOrders G
end Low6966Allocation

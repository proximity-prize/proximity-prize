import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960RetainedCount
import ProximityPrize.SubmissionLower.R6960Low6960Mass0
import ProximityPrize.SubmissionLower.R6960Low6960Mass1
import ProximityPrize.SubmissionLower.R6960Low6960Mass2
import ProximityPrize.SubmissionLower.R6960Low6960Mass3
import ProximityPrize.SubmissionLower.R6960Low6960Mass4
import ProximityPrize.SubmissionLower.R6960Low6960Mass5
import ProximityPrize.SubmissionLower.R6960Low6960Mass6
import ProximityPrize.SubmissionLower.R6960Low6960Mass7
import ProximityPrize.SubmissionLower.R6960Low6960Mass8
import ProximityPrize.SubmissionLower.R6960Low6960Mass9
import ProximityPrize.SubmissionLower.R6960Low6960Mass10
import ProximityPrize.SubmissionLower.R6960Low6960Mass11
import ProximityPrize.SubmissionLower.R6960Low6960Mass12
import ProximityPrize.SubmissionLower.R6960Low6960Mass13
import ProximityPrize.SubmissionLower.R6960Low6960Mass14
import ProximityPrize.SubmissionLower.R6960Low6960Mass15
import ProximityPrize.SubmissionLower.R6960Low6960Mass16
import ProximityPrize.SubmissionLower.R6960Low6960Mass17
import ProximityPrize.SubmissionLower.R6960Low6960Mass18
import ProximityPrize.SubmissionLower.R6960Low6960Mass19
import ProximityPrize.SubmissionLower.R6960Low6960Mass20
import ProximityPrize.SubmissionLower.R6960Low6960Mass21
import ProximityPrize.SubmissionLower.R6960Low6960Mass22
import ProximityPrize.SubmissionLower.R6960Low6960Mass23

set_option Elab.async false
namespace Low6960Allocation
open K1_13 (Shape)
def bandOrders : ∀ k : Band, List (MassCell k)
  | ⟨0,_⟩ => Low6960Allocation.Group0.orders
  | ⟨1,_⟩ => Low6960Allocation.Group1.orders
  | ⟨2,_⟩ => Low6960Allocation.Group2.orders
  | ⟨3,_⟩ => Low6960Allocation.Group3.orders
  | ⟨4,_⟩ => Low6960Allocation.Group4.orders
  | ⟨5,_⟩ => Low6960Allocation.Group5.orders
  | ⟨6,_⟩ => Low6960Allocation.Group6.orders
  | ⟨7,_⟩ => Low6960Allocation.Group7.orders
  | ⟨8,_⟩ => Low6960Allocation.Group8.orders
  | ⟨9,_⟩ => Low6960Allocation.Group9.orders
  | ⟨10,_⟩ => Low6960Allocation.Group10.orders
  | ⟨11,_⟩ => Low6960Allocation.Group11.orders
  | ⟨12,_⟩ => Low6960Allocation.Group12.orders
  | ⟨13,_⟩ => Low6960Allocation.Group13.orders
  | ⟨14,_⟩ => Low6960Allocation.Group14.orders
  | ⟨15,_⟩ => Low6960Allocation.Group15.orders
  | ⟨16,_⟩ => Low6960Allocation.Group16.orders
  | ⟨17,_⟩ => Low6960Allocation.Group17.orders
  | ⟨18,_⟩ => Low6960Allocation.Group18.orders
  | ⟨19,_⟩ => Low6960Allocation.Group19.orders
  | ⟨20,_⟩ => Low6960Allocation.Group20.orders
  | ⟨21,_⟩ => Low6960Allocation.Group21.orders
  | ⟨22,_⟩ => Low6960Allocation.Group22.orders
  | ⟨23,_⟩ => Low6960Allocation.Group23.orders
  | ⟨n+24,h⟩ => absurd h (by omega)
def Gates : Prop :=
  ∃ G : Shape → ℕ, Low6960RetainedCut.GateBank G ∧ GateTable bandOrders G
end Low6960Allocation

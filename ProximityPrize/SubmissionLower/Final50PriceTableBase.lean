import ProximityPrize.SubmissionLower.KoalaRetainedAssembly
import ProximityPrize.SubmissionLower.KoalaWeightedRate
import ProximityPrize.SubmissionLower.Final50PriceMonotone
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Final50PriceTableBase
open K1_13 (Shape InBox)
open KoalaRetainedCut (contractedPrice)
open Final50Price (physicalPrice physicalPriceOld)
open Final50PriceCaps (Band order allowance activeCap start)
open Final50PriceMonotone (physicalPrice_le_old physicalPrice_anti physical_mono)

theorem contracted_le (x h : Shape) (l K : ℕ) :
    contractedPrice x h l K ≤ physicalPrice x l K := by
  dsimp only [contractedPrice]
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl

abbrev OldReceipt (top : ℕ) (k : Band) (bl jl bh jh t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨bl,jl,0⟩ ∧ physicalPriceOld ⟨bh,jh,t⟩ l ≤ allowance top k bl jl t

abbrev PointReceipt (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧ contractedPrice ⟨b,j,t⟩ (start k) l (activeCap k) ≤ allowance top k b j t


open Final50SharedPrice (Rate)
open KoalaWeightedRate (Allowed)

def Covered (top : ℕ) (k : Band) (a : Shape) : Prop :=
  (∃ l, 0 < l ∧ l ≤ order k a ∧ contractedPrice a (start k) l (activeCap k) ≤ allowance top k a.b a.j a.t) ∨
  ∃ u l, k = .empty ∧ 0 < l ∧ l ≤ order k a ∧ Allowed a u ∧
    Final50SharedPrice.price a l (activeCap k) u ≤ allowance top k a.b a.j a.t

abbrev SharedReceipt (t b j l : ℕ) (u : Rate) : Prop :=
  0 < l ∧ l ≤ order .empty ⟨b,j,t⟩ ∧ Allowed ⟨b,j,t⟩ u ∧
    Final50SharedPrice.price ⟨b,j,t⟩ l (activeCap .empty) u ≤ allowance t .empty b j t




end Final50PriceTableBase

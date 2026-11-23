import ProximityPrize.SubmissionLower.R6960Low6960RetainedPhysicalBank
import ProximityPrize.SubmissionLower.R6960Low6960Order

set_option autoImplicit false
set_option Elab.async false
namespace Low6960RetainedCut
noncomputable section
open Low6960Prices (Messages ActiveFits layerWidth layerNeed)
open K1_13 (Row)
open P3 (I K)
open scoped Polynomial

private theorem tapered_active (P : Row 4) (h : PrimaryTaper.JetsBounded P) : ActiveFits P 5164 :=
  fun m hm => (PrimaryTaperActive.of_jets h m hm).trans (by decide)

private theorem bank_contact : AllContact PrimaryTaper.JetsBounded := by
  intro w T P hT hp S hs hits
  obtain ⟨H,hH,hh⟩ := hits
  exact Low6960OrderProof_1.order_of_contact w P hT hp.2.1 hp.2.2.2 hs hH hh

def Bank.of_messages {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s) :
    Bank Γ s := physicalBank hm PrimaryTaper.JetsBounded tapered_active bank_contact

theorem Bank.of_messages_row {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s) :
    (Bank.of_messages hm).row = Low6960OrderProof.BankRow w := rfl

theorem Bank.of_messages_ranked_of_rank {w : I → K} {Γ : Finset K} {s : K → K[X]}
    (hm : Messages w Γ s) (hr : Low6960Order.PrimaryRank w) :
    (Bank.of_messages hm).Ranked := by
  apply physicalBank_ranked hm PrimaryTaper.JetsBounded tapered_active bank_contact
    (rank := Low6960Order.sourceRank)
  · apply sufficient_rank (show Low6960Order.sourceRank / layerWidth + 1 = layerNeed from
      Low6960Order.certified_layers)
    rw [Low6960Order.sourceRank_eq]
    decide
  · exact fun x hx => Low6960Order.symbol_families w x hr hx
  · exact fun x e he hi => PrimaryTaper.symbol_rank x e he hi

theorem Bank.of_messages_ranked {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s) :
    (Bank.of_messages hm).Ranked :=
  Bank.of_messages_ranked_of_rank hm (Low6960Order.primary_rank w)

#print axioms Bank.of_messages
#print axioms Bank.of_messages_ranked_of_rank
#print axioms Bank.of_messages_ranked
end
end Low6960RetainedCut

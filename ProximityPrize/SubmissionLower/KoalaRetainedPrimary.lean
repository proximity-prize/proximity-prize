import ProximityPrize.SubmissionLower.KoalaRetainedPhysicalBank
import ProximityPrize.SubmissionLower.Final50Order

set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open Final50Price (Messages ActiveFits layerWidth layerNeed)
open K1_13 (Row)
open P3 (I K)
open scoped Polynomial

private theorem tapered_active (P : Row 4) (h : PrimaryTaper.JetsBounded P) : ActiveFits P 5164 :=
  fun m hm => (PrimaryTaperActive.of_jets h m hm).trans (by decide)

private theorem bank_contact : AllContact PrimaryTaper.JetsBounded := by
  intro w T P hT hp S hs hits
  obtain ⟨H,hH,hh⟩ := hits
  exact Final50OrderProof_1.order_of_contact w P hT hp.2.1 hp.2.2.2 hs hH hh

def Bank.of_messages {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s) :
    Bank Γ s := physicalBank hm PrimaryTaper.JetsBounded tapered_active bank_contact

theorem Bank.of_messages_row {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s) :
    (Bank.of_messages hm).row = Final50OrderProof.BankRow w := rfl

theorem Bank.of_messages_ranked_of_rank {w : I → K} {Γ : Finset K} {s : K → K[X]}
    (hm : Messages w Γ s) (hr : Final50Order.PrimaryRank w) :
    (Bank.of_messages hm).Ranked := by
  apply physicalBank_ranked hm PrimaryTaper.JetsBounded tapered_active bank_contact
    (rank := Final50Order.sourceRank)
  · apply sufficient_rank (show Final50Order.sourceRank / layerWidth + 1 = layerNeed from
      Final50Order.certified_layers)
    rw [Final50Order.sourceRank_eq]
    decide
  · exact fun x hx => Final50Order.symbol_families w x hr hx
  · exact fun x e he hi => PrimaryTaper.symbol_rank x e he hi

theorem Bank.of_messages_ranked {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s) :
    (Bank.of_messages hm).Ranked :=
  Bank.of_messages_ranked_of_rank hm (Final50Order.primary_rank w)

#print axioms Bank.of_messages
#print axioms Bank.of_messages_ranked_of_rank
#print axioms Bank.of_messages_ranked
end
end KoalaRetainedCut

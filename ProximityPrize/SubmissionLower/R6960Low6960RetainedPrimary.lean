import ProximityPrize.SubmissionLower.R6960Low6960RetainedCount
import ProximityPrize.SubmissionLower.R6960Low6960Retained

set_option Elab.async false

-- merged module R6960Low6960RetainedPhysicalBank
section Merged_R6960Low6960RetainedPhysicalBank

set_option autoImplicit false
set_option Elab.async false
namespace Low6960RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Geom Row shape InBox extend embed Contact OrderAt)
open Low6960Prices (Messages physicalDegree TrueWeightLE ActiveFits primaryBox primaryCutoff
  agreement layerWidth layerNeed)
open K1_13_3 (symbolAt)
open Polynomial
open scoped Polynomial BigOperators

/-- The accepted Low6960OrderProof.BankRow, abstracting only the published taper predicate. -/
def physicalRow (jets : Row 4 → Prop) (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ jets P ∧ Contact w P

def AllContact (jets : Row 4 → Prop) : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → physicalRow jets w T P →
    ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree →
    (∃ H : Finset I, agreement ≤ H.card ∧ ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
    OrderAt P S (levelOrder T)

def physicalBank {w Γ s} (hm : Messages w Γ s) (jets : Row 4 → Prop)
    (active : ∀ P, jets P → ActiveFits P 5164) (contact : AllContact jets) : Bank Γ s where
  row := physicalRow jets w
  bounds T hT P hP := ⟨hP.1,fun m hm => (hP.2.1 m hm).trans hT,active P hP.2.2.1⟩
  order T hT P hP γ hγ := by
    apply contact w T P hT hP
    · simpa only [extend,natDegree_map_eq_of_injective (RingHom.injective embed)] using hm.degree γ hγ
    · obtain ⟨H,hH,hh⟩ := hm.hits γ hγ
      refine ⟨H,hH,fun i hi => ?_⟩
      rw [extend,eval_map,eval₂_at_apply,hh i hi]

theorem physicalBank_ranked {w Γ s} (hm : Messages w Γ s) (jets : Row 4 → Prop)
    (active : ∀ P, jets P → ActiveFits P 5164) (contact : AllContact jets)
    {rank : ℕ} (enough : layerWidth*(layerNeed-1) < rank)
    (families : ∀ x : Geom, (∀ i : I, x ≠ embed (node i)) →
      ∃ r : ℕ → ℕ, rank ≤ ∑ T ∈ Finset.range (primaryCutoff+1), r T ∧
        ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4, (∀ i, physicalRow jets w T (e i)) ∧
          LinearIndependent Geom (fun i => symbolAt x (e i)))
    (symbols : ∀ {n} (x : Geom) (e : Fin n → Row 4), (∀ i, jets (e i)) →
      LinearIndependent Geom (fun i => symbolAt x (e i)) → n ≤ Low6960Prices.symbolCount) :
    (physicalBank hm jets active contact).Ranked := by
  intro x hx
  obtain ⟨r,hr,he⟩ := families x hx
  refine ⟨r,enough.trans_le hr,?_⟩
  intro T hT
  obtain ⟨e,hes,hei⟩ := he T hT
  exact ⟨symbols x e (fun i => (hes i).2.2.1) hei,e,hes,hei⟩

/-- The published floor-plus-one layer identity, with the nonzero remainder required for strict rank. -/
theorem sufficient_rank {rank width need : ℕ} (h : rank/width+1=need)
    (positive_remainder : 0 < rank%width) : width*(need-1)<rank := by
  rw [← h,Nat.add_sub_cancel]
  have total := Nat.mod_add_div rank width
  omega

#print axioms physicalBank_ranked
end
end Low6960RetainedCut

end Merged_R6960Low6960RetainedPhysicalBank

-- merged module R6960Low6960RetainedPrimary
section Merged_R6960Low6960RetainedPrimary

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

def Bank.of_messages {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s) :
    Bank Γ s := physicalBank hm PrimaryTaper.JetsBounded tapered_active bank_contact

theorem Bank.of_messages_row {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s) :
    (Bank.of_messages hm).row = Low6960OrderProof.BankRow w := rfl

theorem Bank.of_messages_ranked_of_rank {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)}
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

theorem Bank.of_messages_ranked {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s) :
    (Bank.of_messages hm).Ranked :=
  Bank.of_messages_ranked_of_rank hm (Low6960Order.primary_rank w)

#print axioms Bank.of_messages
#print axioms Bank.of_messages_ranked_of_rank
#print axioms Bank.of_messages_ranked
end
end Low6960RetainedCut

end Merged_R6960Low6960RetainedPrimary

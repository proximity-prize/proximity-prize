import ProximityPrize.SubmissionLower.R6960Low6960RetainedBank

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
    ∀ S : Geom[X], S.natDegree ≤ physicalDegree →
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

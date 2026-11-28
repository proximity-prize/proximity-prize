import ProximityPrize.SubmissionLower.Z6970H2307PriceDefs
import ProximityPrize.SubmissionLower.Z6969Pack0850
import ProximityPrize.SubmissionLower.Z6970H2307Inventory

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Height2307Count6970
noncomputable section
open P3 (I K)
open K1_13 (Geom Row Shape shape InBox extend atJet OnFactor)
open Low6969Prices (Messages activeFitsPrice ActiveFits SmallFactor Fits Holds FatEquations
  ProperCut lowerCap fullCap TrueWeightLE anchorCutoff)
open Final50GeoCover (activeDegree)
open K1_13_1 (anchorLead indexDegree_eq)
open LowProfile6969 (factor_small lower_of_anchor)
open KoalaRetainedCut (anchor_factors priority_pieces)
open K1_13_1 (index_bounds)
open MvPolynomial
open scoped Polynomial BigOperators
open Low6969RetainedCut (Bank sumShape shape_of_product contractedPrice)
open Height2307Inventory (LayerBudget layerNeed layerWidth)

def GateProof (G : Shape → ℕ) (Gated : ℕ → Shape → Prop) : Prop :=
  ∀ {w Γ s f l}, Messages w Γ s → SmallFactor f →
    (∀ γ∈Γ, OnFactor f (extend (s γ))) → 0<l → ProperCut f Γ s l →
    f.degreeOf 3 < K1.p → ∀ id, Gated id (shape f) → Γ.card ≤ gatePrice G (shape f) l

structure AllocationData (Γ : Finset K) (s : K → (Polynomial K)) (E : FatEquations) (top anchorK : ℕ)
    (G : Shape → ℕ) (Gated : ℕ → Shape → Prop) where
  n : ℕ
  f : Fin n → Row 4
  pieces : Fin n → Finset K
  orders : Fin n → ℕ
  zeros : Finset (Fin n)
  zero_iff : ∀ i, i∈zeros ↔ orders i=0
  small : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits top (fun i => shape (f i))
  active_budget : (∑ i, activeDegree (f i)) ≤ anchorK
  layers : LayerBudget (fun i => shape (f i)) orders
  subset : ∀ i, pieces i ⊆ Γ
  on_factor : ∀ i γ, γ ∈ pieces i → OnFactor (f i) (extend (s γ))
  fat : ∀ i γ, γ ∈ pieces i → Holds E (extend (s γ))
  proper : ∀ i, 0 < orders i → ProperCut (f i) Γ s (orders i)
  contracted : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active, ActiveFits (f i) active →
    ∀ h, InBox h (sumShape zeros (fun j => shape (f j))) →
      (pieces i).card ≤ contractedPrice (shape (f i)) h l active
  gated : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active, ActiveFits (f i) active →
    ∀ id, Gated id (shape (f i)) → (pieces i).card ≤ gatePrice G (shape (f i)) l

def Allocation (budget anchorK : ℕ) (G : Shape → ℕ) (Gated : ℕ → Shape → Prop) : Prop :=
  ∀ {w Γ s}, Messages w Γ s → ∀ top, top ≤ 16 → ∀ E,
    ∀ (d : AllocationData Γ s E top anchorK G Gated) (lowCost : ℕ), lowCost ≤ lowerCap top →
      lowCost + (∑ i, (d.pieces i).card) ≤ budget

theorem count_of_data {budget anchorK : ℕ} {G : Shape → ℕ} {Gated : ℕ → Shape → Prop} (gate : GateProof G Gated)
    (allocate : Allocation budget anchorK G Gated)
    {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s)
    (hceil : layerWidth*(layerNeed-1) < ExpandedOrderH2307.sourceRank) (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) (fullCap 16)) (hw : TrueWeightLE P anchorCutoff)
    (ha : ActiveFits P anchorK) (hz : ∀ γ∈Γ, atJet P (extend (s γ))=0)
    (lower : ∀ top ≤ 16, Low6969Prices.c5 top)
    (book : Finset K) (E : FatEquations) (booked : book.card ≤ 59600)
    (hE : ∀ γ∈Γ, γ∉book → Holds E (extend (s γ))) : Γ.card ≤ 59600+budget := by
  classical
  let bank := Height2307Inventory.bank hm
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := anchor_factors hP
  let top := (shape P).t
  have htop : top ≤ 16 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ anchorK :=
    (sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ) Finset.univ f hP prodDvd).trans
      ((Final50GeoCover.activeFits_iff P anchorK).mp ha)
  let orders i := bank.availability (f i)
  let z := Finset.univ.filter fun i => orders i=0
  have hzero (i) : i∈z ↔ orders i=0 := by simp [z]
  obtain ⟨low,pieces,lowSub,lowOn,sub,on,off,total⟩ := priority_pieces
    (fun i => (factors i).2.2) s book z (fun γ hγ => covers _ (hz γ hγ))
  have lbound := lower top htop _ _ _ (hm.mono lowSub) _ (lower_of_anchor P hP hbox hw) lowOn
  have hchar (i) : (f i).degreeOf 3 < K1.p := (small i).2.2.1.2.2.trans_lt (by decide : 16<K1.p)
  let data : AllocationData Γ s E top anchorK G Gated := {
    n := n, f := f, pieces := pieces, orders := orders, zeros := z, zero_iff := hzero
    small := small, different := different, fits := fits, active_budget := active
    layers := Height2307Inventory.layer_budget hm hceil f (fun i => (factors i).1) different, subset := sub
    on_factor := fun i γ h => (on i γ h).2
    fat := fun i γ h => hE γ (sub i h) (on i γ h).1
    proper := fun i hp => bank.proper_cut (small i) (hchar i) hp le_rfl
    contracted := by
      intro i hi l hp hl K hK h hfloor
      apply bank.companion_price_floor hm f small different z (fun j hj => (hzero j).mp hj) hi
        hp hl hK (hchar i) (pieces i) (sub i) (fun γ hγ => (on i γ hγ).2) (off i hi) h
      rwa [shape_of_product z f (fun i _ => (factors i).1.ne_zero)]
    gated := by
      intro i hi l hp hl K hK id hg
      obtain ⟨Q,hpQ,hboxQ,hwQ,haQ,hcutQ⟩ := bank.proper_cut (small i) (hchar i) hp hl
      exact gate (hm.mono (sub i)) (small i) (fun γ hγ => (on i γ hγ).2) hp
        ⟨Q,hpQ,hboxQ,hwQ,haQ,fun γ hγ e he => hcutQ γ (sub i hγ) e he⟩ (hchar i) id hg
  }
  have counts := allocate hm top htop E data low.card lbound
  change low.card + (∑ i, (pieces i).card) ≤ budget at counts
  exact total.trans (by omega)

end
end Height2307Count6970

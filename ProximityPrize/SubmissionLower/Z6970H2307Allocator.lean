import ProximityPrize.SubmissionLower.Z6970H2307PointAPI
import ProximityPrize.SubmissionLower.Z6970H2307Bands
import ProximityPrize.SubmissionLower.Z6970H2307Inventory

set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
set_option Elab.async false

namespace Height2307Allocation
open K1_13 (Shape InBox FatEligible shape)
open K1_13_8 (Valid zeroShape)
open Low6969Prices (fatPrice Fits fullCap)
open Low6969RetainedCut (contractedPrice)
open Height2307Inventory (LayerBudget availableMass layerNeed)
open Height2307Bands
open P3_6_8 (shapeSum shapeSum_empty shapeSum_insert shapeSum_union shapeSum_mono inBox_trans inBox_shapeSum shapeSum_valid_or_empty)
open scoped BigOperators Classical

def Exclusions : Prop :=
  availableMass ⟨28,3,1⟩ zeroShape 0 < layerNeed ∧
  availableMass ⟨3,9,1⟩ zeroShape 0 < layerNeed ∧
  availableMass ⟨26,4,1⟩ zeroShape 0 < layerNeed ∧
  availableMass ⟨23,5,1⟩ zeroShape 0 < layerNeed ∧
  availableMass ⟨20,6,1⟩ zeroShape 0 < layerNeed ∧
  availableMass ⟨15,7,1⟩ zeroShape 0 < layerNeed ∧
  availableMass ⟨8,8,1⟩ zeroShape 0 < layerNeed

theorem no_cut_shape (excluded : Exclusions) {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i, Valid (a i)) (hl : LayerBudget a l)
    (z : Finset (Fin n)) (hz : ∀ i ∈ z, l i = 0) :
    z = ∅ ∨ (Box (shapeSum a z) ∧ Valid (shapeSum a z)) := by
  rcases shapeSum_valid_or_empty ha z with empty | valid
  · exact Or.inl empty
  right
  let r := shapeSum a z
  change Box r ∧ Valid r
  change Valid r at valid
  have hj : 0 < r.j := by
    obtain ⟨ht,hjt,_⟩ := valid
    omega
  have hmass := Height2307Inventory.mass_le hl (s := ∅) (q := r) (L := 0)
    hz (by simp) (by simp) (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
  rw [shapeSum_empty] at hmass
  have need := hmass.trans (Height2307Inventory.full_le_available (show 0<r.j+zeroShape.j by exact hj))
  have reject {b j : ℕ} (hb : b≤r.b) (hj' : j≤r.j) (small : 0<j)
      (mass : availableMass ⟨b,j,1⟩ zeroShape 0 < layerNeed) : False := by
    have h := Height2307Inventory.availableMass_anti
      (show InBox ⟨b,j,1⟩ r from ⟨hb,hj',valid.1⟩)
      (show zeroShape.b≤zeroShape.b ∧ zeroShape.j≤zeroShape.j from ⟨le_rfl,le_rfl⟩)
      (le_refl 0) (show 0<j+zeroShape.j by exact small)
    exact (not_lt_of_ge (need.trans h)) mass
  rcases excluded with ⟨e3,e9,e4,e5,e6,e7,e8⟩
  have hv := valid.2.2
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,valid⟩
  · by_contra! h; exact reject (by omega) ((Nat.mul_le_mul_left 3 valid.1).trans valid.2.1) (by decide) e3
  · by_contra! h; exact reject (by omega) (by omega) (by decide) e9
  · intro h; by_contra! h'; exact reject (by omega) h (by decide) e4
  · intro h; by_contra! h'; exact reject (by omega) h (by decide) e5
  · intro h; by_contra! h'; exact reject (by omega) h (by decide) e6
  · intro h; by_contra! h'; exact reject (by omega) h (by decide) e7
  · intro h; by_contra! h'; exact reject (by omega) h (by decide) e8

def OrderValid (order : Order) : Prop :=
  ∀ k x, Valid x → InBox ((start k).plus x) (fullCap 16) →
    0 < order k x ∧ (order k x = 1 ∨ availableMass (start k) x (order k x-1) < layerNeed)

theorem total {G : Shape → ℕ} {Gated : ℕ → Shape → Prop}
    {order : Order} {book : Band → Shape → Option ℕ}
    (excluded : Exclusions) (validOrder : OrderValid order) (companion : Companion order book)
    (table : PointTable order book G Gated)
    (top : ℕ) (htop : top≤16) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (lowCost : ℕ) (hlow : lowCost≤Low6969Prices.lowerCap top)
    (hfits : Fits top a) (hstrong : ∀ i, (a i).j≤2*(a i).b+(a i).t) (hlayers : LayerBudget a l)
    (hphys : ∀ i m, 0<m → m≤l i → ∀ k, Admits k (shapeSum a (Finset.univ.filter (fun i => l i=0))) →
      cost i≤contractedPrice (a i) (start k) m 179)
    (hshared : ∀ i m u, 0<m → m≤l i → Low6969SharedPrice.RateFits (a i) u →
      cost i≤Low6969SharedPrice.price (a i) m 179 u)
    (hgate : ∀ i m, 0<m → m≤l i → ∀ k : Band, Gated k.val (a i) →
      cost i≤Height2307Count6970.gatePrice G (a i) m)
    (hfat : ∀ i, FatEligible (a i) → cost i≤fatPrice (a i)) :
    lowCost+(∑ i,cost i)≤budget := by
  let z := Finset.univ.filter (fun i => l i = 0)
  let pos := Finset.univ.filter (fun i => ¬ l i = 0)
  let r := P3_6_8.shapeSum a z
  have ha (i : Fin n) : Valid (a i) := hfits.1 i
  have hz (i : Fin n) (hi : i ∈ z) : l i = 0 := (Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ k : Band, Admits k r ∧
      (∑ i ∈ z, cost i) ≤ reserve k := by
    rcases no_cut_shape excluded a l ha hlayers z hz with hempty | ⟨hret,hr⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨empty,hr0.symm ▸ empty_admits,?_⟩
      rw [hempty,Finset.sum_empty]
      omega
    · obtain ⟨k,hk⟩ := choose_band r hr hret
      exact ⟨k,hk,retained_cost ha hr hret hk hfat⟩
  obtain ⟨k,hk,hcost⟩ := account
  let q := start k
  have hqr : InBox q r := admits_floor hk
  have hreserve : reserve k ≤ factorCap top := reserve_fits top htop k
  have hall : InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top) := hfits.2
  have member_cap {s : Finset (Fin n)} (hs : s ⊆ pos) :
      InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top) := by
    have hb := P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _, Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have order_le (i : Fin n) (hi : i∈pos) :
      InBox (q.plus (a i)) (fullCap top) ∧ 0<order k (a i) ∧ order k (a i)≤l i := by
    have hone : shapeSum a {i} = a i := by
      rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl,
        shapeSum_insert a (by simp),shapeSum_empty]
      cases a i
      simp [zeroShape, Shape.plus]
    have hsingle : ({i} : Finset (Fin n)) ⊆ pos := Finset.singleton_subset_iff.mpr hi
    have hc := member_cap hsingle
    rw [hone] at hc
    have goal : InBox (q.plus (a i)) (fullCap 16) := ⟨hc.1,hc.2.1,hc.2.2.trans htop⟩
    obtain ⟨hp,hh⟩ := validOrder k (a i) (ha i) goal
    refine ⟨hc,hp,?_⟩
    rcases hh with one | small
    · rw [one]; exact hpos i hi
    · have hj0 := (ha i).2.1
      have hj : 0 < q.j+(a i).j := by have := (ha i).1; omega
      have hmass := Height2307Inventory.mass_le hlayers hz (s := {i}) (L := l i)
        (by simp) (hdisj hsingle) hqr
      rw [hone] at hmass
      refine le_of_not_gt fun hbad => ?_
      have mm := Height2307Inventory.availableMass_mono_order hj
        (show l i≤order k (a i)-1 by omega)
      exact (not_lt_of_ge ((hmass.trans (Height2307Inventory.full_le_available hj)).trans mm)) small
  have hfits_pos := member_cap (s := pos) (Finset.Subset.rfl)
  have hwidth : (∑ i ∈ pos, (a i).b) ≤ 143 - q.b := by
    have hh := hfits_pos.1
    change q.b + (∑ i ∈ pos, (a i).b) ≤ 143 at hh
    omega
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 60 - q.j := by
    have hh := hfits_pos.2.1
    change q.j + (∑ i ∈ pos, (a i).j) ≤ 60 at hh
    omega
  have hDen : 0 < pricingDenom k := denom_pos k
  have hweights : (∑ i ∈ pos, pricingWeight k (a i).b (a i).j (a i).t) ≤ pricingDenom k := by
    by_cases he : k = empty
    · subst k
      change (∑ i∈pos,Low6969AllocWeight.weight (a i).b (a i).j (a i).t) ≤ 383
      exact Low6969AllocWeight.sum_le htop a hfits pos
    · by_cases htier : tiered k
      · simpa [q, pricingWeight, pricingDenom, he, htier] using
          (Research6966.LowTierWeight.total pos (fun i => (a i).j) hindex)
      · simpa [q, pricingWeight, pricingDenom, he, htier] using hindex
  let C := factorCap top - reserve k
  let M := pricingDenom k
  have hp : lowCost + (∑ i ∈ pos, cost i) + reserve k ≤ budget := by
    by_cases positive_fee : ∀ i ∈ pos, cost i ≤ allowance k top (a i).b (a i).j (a i).t
    · have fees (i : Fin n) (hi : i ∈ pos) : M*cost i ≤ C * pricingWeight k (a i).b (a i).j (a i).t := by
        have h := Nat.mul_le_mul_left M (positive_fee i hi)
        change M*cost i ≤ M*(C*pricingWeight k (a i).b (a i).j (a i).t / M) at h
        calc
          _ ≤ M*(C*pricingWeight k (a i).b (a i).j (a i).t / M) := h
          _ = (C*pricingWeight k (a i).b (a i).j (a i).t / M)*M := Nat.mul_comm _ _
          _ ≤ _ := Nat.div_mul_le_self _ _
      have hweighted : M * (∑ i ∈ pos, cost i) ≤ M*C := by
        rw [Finset.mul_sum, mul_comm M C]
        refine (Finset.sum_le_sum fees).trans ?_
        rw [← Finset.mul_sum]
        exact Nat.mul_le_mul_left _ hweights
      have hc : (∑ i ∈ pos, cost i) ≤ C := Nat.le_of_mul_le_mul_left hweighted hDen
      have hb : Low6969Prices.lowerCap top ≤ budget := by
        interval_cases top <;> decide
      dsimp [C, factorCap] at hc hreserve
      omega
    · push_neg at positive_fee
      obtain ⟨i,hi,hgt⟩ := positive_fee
      obtain ⟨hc,hop,hol⟩ := order_le i hi
      have htop' : q.t+(a i).t≤top := hc.2.2
      have goal : InBox (q.plus (a i)) (fullCap 16) := ⟨hc.1,hc.2.1,hc.2.2.trans htop⟩
      obtain ⟨m,fee,hmp,hml,hfee,paid⟩ := table k (a i) (ha i) (hstrong i) goal
      have charge : cost i≤fee := by
        rcases hfee with hw | ⟨u,hu,hw⟩ | ⟨hg,hw⟩
        · exact (hphys i m hmp (hml.trans hol) k hk).trans hw
        · exact (hshared i m u hmp (hml.trans hol) hu).trans hw
        · exact (hgate i m hmp (hml.trans hol) k hg).trans hw
      rcases paid with p | ⟨debt,hbook,hpaid⟩
      · exact (not_lt_of_ge (charge.trans (p.trans (allowance_mono k htop' htop))) hgt).elim
      · let partners := pos.erase i
        have bounds (g : Shape → ℕ) :
            (∑ v∈partners,g (a v))+g (a i) = ∑ v∈pos,g (a v) :=
          Finset.sum_erase_add pos (fun v => g (a v)) hi
        have eb := bounds Shape.b
        have ej := bounds Shape.j
        have et := bounds Shape.t
        have hT := hfits_pos.2.2
        change q.t+(∑ v∈pos,(a v).t)≤top at hT
        have hfit : InBox (shapeSum a partners) (residual k (a i)) := by
          refine ⟨?_,?_,?_⟩
          · change (∑ v∈partners,(a v).b)≤143-q.b-(a i).b; omega
          · change (∑ v∈partners,(a v).j)≤60-q.j-(a i).j; omega
          · change (∑ v∈partners,(a v).t)≤16-q.t-(a i).t; omega
        have hcosts := companion hbook a cost partners (fun v _ => ⟨ha v,hstrong v⟩) hfit
          (fun v hv => by
            have ⟨_,hvp,hvl⟩ := order_le v (Finset.mem_of_mem_erase hv)
            exact hphys v _ hvp hvl k hk)
        have ec := Finset.sum_erase_add pos cost hi
        change (∑ v∈partners,cost v)+cost i = ∑ v∈pos,cost v at ec
        change fee+debt+reserve k+Low6969Prices.lowerCap (q.t+(a i).t)≤budget at hpaid
        have hcap := factorCap_mono htop' htop
        change budget-Low6969Prices.lowerCap (q.t+(a i).t) ≤ budget-Low6969Prices.lowerCap top at hcap
        have hb : Low6969Prices.lowerCap top ≤ budget := by interval_cases top <;> decide
        have hb' : Low6969Prices.lowerCap (q.t+(a i).t) ≤ budget := by
          have h := htop'.trans htop
          generalize q.t+(a i).t = t at *
          interval_cases t <;> decide
        omega
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  omega

end Height2307Allocation

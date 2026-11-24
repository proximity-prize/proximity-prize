import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Retained
import ProximityPrize.SubmissionLower.R6961Low6961RetainedFees

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Low6961AllocTotal
open K1_13 (Shape InBox FatEligible)
open Low6961RetainedCut (contractedPrice)
open K1_13_8 (Valid zeroShape)
open Final50PriceLayer (availableMass)
open Low6961Prices (physicalPrice fatPrice)
open Low6961Prices (layerNeed LayerBudget fullCap Fits)
open Low6961Allocation
open Low6961Retained (Box)
open Low6961Monotone (physicalPrice_anti)
open Lower6961.Low (retained_family_fee)
open Lower6961.Low (degree_bound)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_insert shapeSum_union shapeSum_mono inBox_trans inBox_shapeSum shapeSum_valid_or_empty)

def retainedShape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Shape :=
  P3_6_8.shapeSum a (Finset.univ.filter fun i => l i = 0)

private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} {k : Band} (ha : ∀ i, Valid (a i)) (hr : Valid (P3_6_8.shapeSum a z))
    (hbox : Box (P3_6_8.shapeSum a z)) (hk : Admits k (P3_6_8.shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤ reserve k := by
  let r := P3_6_8.shapeSum a z
  let er := z.equivFin.symm
  let ar : Fin z.card → Shape := fun i => a (er i).val
  have sums (g : Shape → ℕ) : (∑ i, g (ar i)) = ∑ i ∈ z, g (a i) := by
    rw [← Finset.sum_attach z (fun i => g (a i))]
    exact Fintype.sum_equiv er _ _ fun _ => rfl
  have hj : (∑ i, (ar i).j) ≤ 7 := by rw [sums]; exact hbox.2.1
  have hb : (∑ i, (ar i).b) ≤ Final50FatReserve.degreeCap (∑ i, (ar i).j) := by
    rw [sums, sums]
    exact degree_bound hr hbox
  have hp := retained_family_fee z.card ar (fun i => ha (er i).val) hj hb
  rw [sums, sums, sums, sums] at hp
  have hp' : (∑ i ∈ z, fatPrice (a i)) ≤
      Lower6961.Low.retainedTariff r.b r.j r.t := hp
  refine (Finset.sum_le_sum fun i hi => hfat i ?_).trans (hp'.trans (admits_fee hk))
  have h := P3_6_8.inBox_shapeSum a hi
  exact ⟨(h.1.trans hbox.1).trans (by decide), (h.2.1.trans hbox.2.1).trans (by decide)⟩

/-- Total cost of all factors in the low-height cover. -/
theorem total (receipts : ∀ k : Band, Receipt k) (top : ℕ) (htop : top ≤ 14) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (hfits : Fits top a) (hlayers : LayerBudget a l)
    (hphys : ∀ i m, 0 < m → m ≤ l i → ∀ k, Admits k (retainedShape a l) →
      cost i ≤ contractedPrice (a i) (start k) m 165)
    (hshared : ∀ i m u, 0 < m → m ≤ l i → Low6961WeightedRate.Allowed (a i) u →
      cost i ≤ Low6961SharedPrice.price (a i) m 165 u)
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i, cost i) ≤ factorCap top := by
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
    rcases Low6961Retained.no_cut_shape a l ha hlayers z hz with hempty | ⟨hret, htr, _⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨empty,hr0.symm ▸ empty_admits,?_⟩
      rw [hempty,Finset.sum_empty]
      omega
    · have hr : Valid r := (P3_6_8.shapeSum_valid_or_empty ha z).resolve_left (by
        intro he
        have heq : P3_6_8.shapeSum a z = zeroShape := he ▸ P3_6_8.shapeSum_empty a
        have hpos : 1 ≤ (P3_6_8.shapeSum a z).t := htr
        rw [heq] at hpos
        exact (by decide : ¬ (1 ≤ zeroShape.t)) hpos)
      obtain ⟨k,hk⟩ := choose_band r hr hret
      exact ⟨k,hk,retained_cost ha hr hret hk hfat⟩
  obtain ⟨k,hk,hcost⟩ := account
  let q := start k
  have hqr : InBox q r := admits_floor hk
  have massKind : q = zeroShape ∨ 0 < q.j := start_flat k
  have hreserve : reserve k ≤ factorCap top := reserve_fits top htop k
  have hall : InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top) := hfits.2
  have member_cap {s : Finset (Fin n)} (hs : s ⊆ pos) :
      InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top) := by
    have hb := P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _, Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have positive_fee (i : Fin n) (hi : i ∈ pos) :
      cost i ≤ allowance k top (a i).b (a i).j (a i).t := by
    have hone : P3_6_8.shapeSum a {i} = a i := by
      rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl,
        P3_6_8.shapeSum_insert a (by simp),P3_6_8.shapeSum_empty]
      cases a i
      simp [zeroShape, Shape.plus]
    have hsingle : ({i} : Finset (Fin n)) ⊆ pos := Finset.singleton_subset_iff.mpr hi
    have hL : 0 < l i := hpos i hi
    have hj0 : 0 < (a i).j := by
      obtain ⟨ht, hj, _⟩ := ha i
      omega
    have hj : 0 < q.j + (a i).j := by omega
    have hmass0 := Low6961Retained.mass_le hlayers hz
      (s := {i}) (L := l i) (by simp) (hdisj hsingle) hqr
    rw [hone] at hmass0
    have hmass := hmass0.trans (layer_le_available massKind hj)
    have horder : order (receipts k).orders (a i) ≤ l i := by
      rcases order_valid (receipts k).orders (a i) with h | h
      · omega
      · by_contra! hn
        have hmono := Final50PriceLayer.availableMass_mono massKind hj
          (show l i ≤ order (receipts k).orders (a i) - 1 by omega)
        exact (not_lt_of_ge (hmass.trans hmono)) h
    have hc := member_cap hsingle
    rw [hone] at hc
    have goal : InBox ((start k).plus (a i)) (fullCap 14) :=
      ⟨hc.1,hc.2.1,hc.2.2.trans htop⟩
    have ht : (start k).t+(a i).t≤top := hc.2.2
    rcases (receipts k).covers (a i) (ha i) goal with ⟨m,hm,hmo,hfee⟩ | ⟨u,m,he,hm,hmo,hu,hfee⟩
    · exact (hphys i m hm (hmo.trans horder) k hk).trans
        (hfee.trans (allowance_mono k ht htop))
    · exact (hshared i m u hm (hmo.trans horder) hu).trans
        (hfee.trans (allowance_mono k (ht.trans' (Nat.le_add_left _ _)) htop))
  have hfits_pos := member_cap (s := pos) (Finset.Subset.rfl)
  have hwidth : (∑ i ∈ pos, (a i).b) ≤ 132 - q.b := by
    have hh := hfits_pos.1
    change q.b + (∑ i ∈ pos, (a i).b) ≤ 132 at hh
    omega
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 55 - q.j := by
    have hh := hfits_pos.2.1
    change q.j + (∑ i ∈ pos, (a i).j) ≤ 55 at hh
    omega
  have hDen : 0 < pricingDenom k := denom_pos k
  have hweights : (∑ i ∈ pos, pricingWeight k (a i).b (a i).j (a i).t) ≤ pricingDenom k := by
    by_cases he : k = empty
    · subst k
      change (∑ i∈pos,KoalaAllocationWeight.weight (a i).b (a i).j (a i).t) ≤ 352
      exact KoalaAllocationWeight.sum_le htop a hfits pos
    · simpa only [q, pricingWeight, pricingDenom, ite_eq_right he] using hindex
  let C := factorCap top - reserve k
  let M := pricingDenom k
  have fees (i : Fin n) (hi : i ∈ pos) : M*cost i ≤ C * pricingWeight k (a i).b (a i).j (a i).t := by
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
  have hp : (∑ i ∈ pos, cost i) ≤ C := Nat.le_of_mul_le_mul_left hweighted hDen
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap top
  dsimp [C] at hp
  omega

#print axioms total
end Low6961AllocTotal

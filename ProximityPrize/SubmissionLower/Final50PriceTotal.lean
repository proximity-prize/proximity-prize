import ProximityPrize.SubmissionLower.Compact50PriceTable
import ProximityPrize.SubmissionLower.Final50PriceMass
import ProximityPrize.SubmissionLower.Final50FatReserve

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Final50PriceTotal
open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape)
open Final50PriceLayer (availableMass)
open Final50Price (physicalPrice fatPrice)
open Final50Price (layerNeed LayerBudget fullCap Fits)
open Final50PriceCaps (factorCap Band reserve start indexBudget Admits activeCap)
open Final50PriceRetained (Box)
open Final50PriceMonotone (physicalPrice_anti)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_insert P3_6_8.shapeSum_union
  P3_6_8.shapeSum_mono P3_6_8.inBox_trans P3_6_8.inBox_shapeSum P3_6_8.shapeSum_valid_or_empty
  from ProximityPrize.SubmissionLower.GoldBranch6N8

def retainedShape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Shape :=
  P3_6_8.shapeSum a (Finset.univ.filter fun i => l i = 0)

private theorem chooseBand (r : Shape) (hr : Valid r) (hx : Box r) : ∃ k, Admits k r := by
  obtain ⟨b,j,t⟩ := r
  have ht : 1 ≤ t := hr.1
  have hjt : 3*t ≤ j := hr.2.1
  have hjb : j ≤ 3*b := hr.2.2
  have hj : j ≤ 7 := hx.2.1
  have ht' : t = 1 ∨ t = 2 := by omega
  rcases ht' with rfl | rfl
  · have hj' : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hj' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.one3, by simp [Admits, start, InBox]; omega⟩
    · exact ⟨.one4, by simp [Admits, start, InBox]; omega⟩
    · exact ⟨.one5, by simp [Admits, start, InBox]; omega⟩
    · exact ⟨.one6, by simp [Admits, start, InBox]; omega⟩
    · exact ⟨.one7, by simp [Admits, start, InBox]; omega⟩
  · have hj' : j = 6 ∨ j = 7 := by omega
    rcases hj' with rfl | rfl
    · by_cases hb : b ≤ 11
      · exact ⟨.two6thin, by simp [Admits, start, InBox, hb]; omega⟩
      · exact ⟨.two6wide, by simp [Admits, start, InBox]; omega⟩
    · exact ⟨.two7, by simp [Admits, start, InBox]; omega⟩

private theorem charge_eq {k : Band} {r : Shape} (h : Admits k r) :
    Final50FatReserve.charge r.b r.j r.t = reserve k := by
  obtain ⟨hb,hj,ht,hsmall,_⟩ := h
  have hb' := hb.1
  rw [hj, ht]
  cases k <;> simp [start, reserve, Final50FatReserve.charge] at * <;> omega

private theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ Final50FatReserve.degreeCap r.j := by
  have hjl : 3 ≤ r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j = 3 ∨ r.j = 4 ∨ r.j = 5 ∨ r.j = 6 ∨ r.j = 7 := by omega
  rcases hj with hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [Final50FatReserve.degreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2 (by omega)

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
  have hp := Final50FatReserve.family z.card ar (fun i => ha (er i).val) hj hb
  rw [sums, sums, sums, sums] at hp
  have hp' : (∑ i ∈ z, fatPrice (a i)) ≤
      Final50FatReserve.charge r.b r.j r.t := hp
  rw [charge_eq hk] at hp'
  refine (Finset.sum_le_sum fun i hi => hfat i ?_).trans hp'
  have h := P3_6_8.inBox_shapeSum a hi
  exact ⟨(h.1.trans hbox.1).trans (by decide), (h.2.1.trans hbox.2.1).trans (by decide)⟩

/-- Total cost of all factors in the low-height cover. -/
theorem total (top : ℕ) (htop : top ≤ 14) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (hfits : Fits top a) (hlayers : LayerBudget a l)
    (hphys : ∀ i, 0 < l i → ∀ k, Admits k (retainedShape a l) →
      cost i ≤ physicalPrice (a i) (l i) (activeCap k))
    (hshared : ∀ i m u, 0 < m → m ≤ l i → Final50SharedPrice.RateFits (a i) u →
      cost i ≤ Final50SharedPrice.price (a i) m 157 u)
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
    rcases Final50PriceRetained.no_cut_shape a l ha hlayers z hz with hempty | ⟨hret, htr, _⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨.empty, ?_, ?_⟩
      · rw [hr0]
        simp [Admits, start, zeroShape, InBox]
      · simp [hempty, reserve]
    · have hr : Valid r := (P3_6_8.shapeSum_valid_or_empty ha z).resolve_left (by
        intro he
        have heq : P3_6_8.shapeSum a z = zeroShape := he ▸ P3_6_8.shapeSum_empty a
        have hpos : 1 ≤ (P3_6_8.shapeSum a z).t := htr
        rw [heq] at hpos
        exact (by decide : ¬ (1 ≤ zeroShape.t)) hpos)
      obtain ⟨k,hk⟩ := chooseBand r hr hret
      exact ⟨k,hk,retained_cost ha hr hret hk hfat⟩
  obtain ⟨k,hk,hcost⟩ := account
  let q := start k
  have hqr : InBox q r := hk.1
  have massKind : q = zeroShape ∨ 0 < q.j := by cases k <;> decide
  have hreserve : reserve k ≤ factorCap top := by interval_cases top <;> cases k <;> decide
  have hall : InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top) := hfits.2
  have member_cap {s : Finset (Fin n)} (hs : s ⊆ pos) :
      InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top) := by
    have hb := P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _, Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have positive_fee (i : Fin n) (hi : i ∈ pos) :
      cost i ≤ Final50PriceCaps.allowance top k (a i).j := by
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
    have hmass0 := Final50PriceRetained.mass_le hlayers hz
      (s := {i}) (L := l i) (by simp) (hdisj hsingle) hqr
    rw [hone] at hmass0
    have hmass := hmass0.trans (Final50PriceLayer.layerSum_le_available massKind hj)
    have horder : Final50PriceCaps.order k (a i) ≤ l i := by
      rcases Final50PriceMass.order_valid k (a i) with h | h
      · omega
      · by_contra! hn
        have hmono := Final50PriceLayer.availableMass_mono massKind hj
          (show l i ≤ Final50PriceCaps.order k (a i) - 1 by omega)
        exact (not_lt_of_ge (hmass.trans hmono)) h
    have hc := member_cap hsingle
    rw [hone] at hc
    rcases Compact50PriceTable.price top htop k (a i) (ha i) hc with hold | ⟨u,m,he,hm,hmo,hu,hfee⟩
    · exact (hphys i hL k hk).trans
        ((physicalPrice_anti _ _ (Final50PriceCaps.order_pos k _) horder).trans hold)
    · have hr : activeCap k = 157 := he ▸ (by decide : activeCap .empty = 157)
      rw [hr] at hfee
      exact (hshared i m u hm (hmo.trans horder) hu).trans hfee
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 52 - q.j := by
    have hh := (member_cap (s := pos) (Finset.Subset.rfl)).2.1
    change q.j + (∑ i ∈ pos, (a i).j) ≤ 52 at hh
    omega
  have hDen : 0 < 52 - q.j := by
    have hh : q.j ≤ 7 := by cases k <;> decide
    omega
  let C := factorCap top - reserve k
  let M := 52 - q.j
  have fees (i : Fin n) (hi : i ∈ pos) : M*cost i ≤ C * (a i).j := by
    have h := Nat.mul_le_mul_left M (positive_fee i hi)
    change M * cost i ≤ M * (C * (a i).j / M) at h
    calc
      M*cost i ≤ M*(C*(a i).j / M) := h
      _ = (C*(a i).j / M)*M := Nat.mul_comm _ _
      _ ≤ C*(a i).j := Nat.div_mul_le_self _ _
  have hweighted : M * (∑ i ∈ pos, cost i) ≤ M*C := by
    rw [Finset.mul_sum, mul_comm M C]
    refine (Finset.sum_le_sum fees).trans ?_
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ hindex
  have hp : (∑ i ∈ pos, cost i) ≤ C := Nat.le_of_mul_le_mul_left hweighted hDen
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap top
  dsimp [C] at hp
  omega

#print axioms total
end Final50PriceTotal

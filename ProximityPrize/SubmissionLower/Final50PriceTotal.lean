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
open Final50FatReserve (oneReserve twoReserve)
open Final50PriceMonotone (physicalPrice_anti)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_insert P3_6_8.shapeSum_union
  P3_6_8.shapeSum_mono P3_6_8.inBox_trans P3_6_8.inBox_shapeSum P3_6_8.shapeSum_valid_or_empty
  from ProximityPrize.SubmissionLower.GoldBranch6N8

def retainedShape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Shape :=
  P3_6_8.shapeSum a (Finset.univ.filter fun i => l i = 0)

private theorem retainedBox_down {a r : Shape} (h : InBox a r) (hr : Box r) :
    Box a := by
  rcases h with ⟨hb, hj, _⟩
  rcases hr with ⟨hrb, hrj, h4, h5, h6, h7⟩
  exact ⟨hb.trans hrb, hj.trans hrj, fun k => hb.trans (h4 (k.trans hj)),
    fun k => hb.trans (h5 (k.trans hj)), fun k => hb.trans (h6 (k.trans hj)), fun k => hb.trans (h7 (k.trans hj))⟩
private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} (hretained : Final50FatReserve.Charges) (ha : ∀ i, Valid (a i)) (hbox : Box (P3_6_8.shapeSum a z))
    (ht : (P3_6_8.shapeSum a z).t = 1 ∨ (P3_6_8.shapeSum a z).t = 2)
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤ if (P3_6_8.shapeSum a z).t = 1 then oneReserve else twoReserve := by
  let r := P3_6_8.shapeSum a z
  change r.t = 1 ∨ r.t = 2 at ht
  change Box r at hbox
  change (∑ i ∈ z, cost i) ≤ if r.t = 1 then oneReserve else twoReserve
  have admitted {i} (hi : i ∈ z) := retainedBox_down (P3_6_8.inBox_shapeSum a hi) hbox
  have paid {i} (hi : i ∈ z) : cost i ≤ fatPrice (a i) :=
    hfat i ⟨(admitted hi).1.trans (by decide), (admitted hi).2.1.trans (by decide)⟩
  rcases ht with ht | ht
  · rw [ite_eq_left ht]
    calc
      _ ≤ ∑ i ∈ z, oneReserve * (a i).t := by
        apply Finset.sum_le_sum
        intro i hi
        have hti : (a i).t ≤ r.t := (P3_6_8.inBox_shapeSum a hi).2.2
        have hai : (a i).t = 1 := by have := (ha i).1; omega
        simpa only [hai, Nat.mul_one] using (paid hi).trans ((hretained _ (ha i) (admitted hi)).1 hai)
      _ = oneReserve := by
        rw [← Finset.mul_sum]
        change oneReserve * r.t = oneReserve
        rw [ht, Nat.mul_one]
  · rw [ite_eq_right (by omega : r.t ≠ 1)]
    have htwo : 2 * (∑ i ∈ z, cost i) ≤ twoReserve * r.t := by
      change 2 * (∑ i ∈ z, cost i) ≤ twoReserve * ∑ i ∈ z, (a i).t
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hti : (a i).t ≤ r.t := (P3_6_8.inBox_shapeSum a hi).2.2
      obtain ⟨hone, hsingle⟩ := hretained _ (ha i) (admitted hi)
      by_cases hai : (a i).t = 2
      · rw [hai, Nat.mul_comm twoReserve 2]
        exact Nat.mul_le_mul_left _ ((paid hi).trans (hsingle hai))
      · have htone : (a i).t = 1 := by have := (ha i).1; omega
        rw [htone, Nat.mul_one]
        exact (Nat.mul_le_mul_left 2 ((paid hi).trans (hone htone))).trans (by decide)
    rw [ht, Nat.mul_comm twoReserve 2] at htwo
    omega
/-- Total cost of all factors in the low-height cover. -/
theorem total (top : ℕ) (htop : top ≤ 13) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (hfits : Fits top a) (hlayers : LayerBudget a l)
    (hphys : ∀ i, 0 < l i → ∀ k, Admits k (retainedShape a l) →
      cost i ≤ physicalPrice (a i) (l i) (activeCap k))
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
      change Box r at hret
      change 1 ≤ r.t at htr
      have hjr : 3 * r.t ≤ r.j := hr.2.1
      have hbr : r.j ≤ 3 * r.b := hr.2.2
      have hrj : r.j ≤ 7 := hret.2.1
      have ht : r.t = 1 ∨ r.t = 2 := by omega
      have paid := retained_cost Final50FatReserve.proof ha hret ht hfat
      change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then oneReserve else twoReserve) at paid
      rcases ht with ht | ht
      · refine ⟨.one, ⟨?_, ht.symm⟩, ?_⟩
        · change 1 ≤ r.b ∧ 3 ≤ r.j ∧ 1 ≤ r.t
          omega
        · rw [ite_eq_left ht] at paid
          exact paid
      · refine ⟨.two, ⟨?_, ht.symm⟩, ?_⟩
        · change 2 ≤ r.b ∧ 6 ≤ r.j ∧ 2 ≤ r.t
          omega
        · rw [ite_eq_right (by omega : r.t ≠ 1)] at paid
          exact paid
  obtain ⟨k,hk,hcost⟩ := account
  let q := start k
  have hqr : InBox q r := hk.1
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
    have hmass := hmass0.trans (Final50PriceLayer.layerSum_le_available hj)
    have horder : Final50PriceCaps.order k (a i) ≤ l i := by
      rcases Final50PriceMass.order_valid k (a i) with h | h
      · omega
      · by_contra! hn
        have hmono := Final50PriceLayer.availableMass_mono hj
          (show l i ≤ Final50PriceCaps.order k (a i) - 1 by omega)
        exact (not_lt_of_ge (hmass.trans hmono)) h
    have hc := member_cap hsingle
    rw [hone] at hc
    exact (hphys i hL k hk).trans
      ((physicalPrice_anti _ _ (Final50PriceCaps.order_pos k _) horder).trans
        (Compact50PriceTable.price top htop k (a i) (ha i) hc))
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 50 - q.j := by
    have hh := (member_cap (s := pos) (Finset.Subset.rfl)).2.1
    change q.j + (∑ i ∈ pos, (a i).j) ≤ 50 at hh
    omega
  have hDen : 0 < 50 - q.j := by
    have hh : q.j ≤ 7 := by cases k <;> decide
    omega
  let C := factorCap top - reserve k
  let M := 50 - q.j
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

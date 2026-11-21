import ProximityPrize.SubmissionLower.Low48PriceTable
import ProximityPrize.SubmissionLower.Low48PriceMass
import ProximityPrize.SubmissionLower.Low48PriceReserve

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Low48PriceTotal
open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape availableMass)
open P0_9_8 (oneStart twoStart symbol_count)
open Low48Price (physicalPrice fatPrice)
open Low48Price (layerNeed LayerBudget fullCap Fits)
open Low48PriceCaps (factorCap Band reserve start indexBudget)
open Low48PriceReserve (oneReserve twoReserve)
open Low48PriceRetained (Box)
open Low48PriceMonotone (physicalPrice_anti)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_insert P3_6_8.shapeSum_union
  P3_6_8.shapeSum_mono P3_6_8.inBox_trans P3_6_8.inBox_shapeSum P3_6_8.shapeSum_valid_or_empty
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private def Bellman (top : ℕ) (r : Shape) (cap : ℕ) : Prop :=
  ∃ (B order : Shape → ℕ), B zeroShape ≤ cap ∧
    (∀ x, Valid x → InBox (r.plus x) (fullCap top) →
      0 < order x ∧
        (order x = 1 ∨ availableMass r x (order x - 1) < layerNeed)) ∧
    (∀ (y a : Shape), (y = zeroShape ∨ Valid y) → Valid a →
      InBox (r.plus (y.plus a)) (fullCap top) →
      physicalPrice a (order (y.plus a)) + B (y.plus a) ≤ B y)
private theorem bellman_of_budget (top : ℕ) (r : Shape) (cap : ℕ) (order : Shape → ℕ)
    (hpos : ∀ x, 0 < order x)
    (hmono : ∀ {a x}, a.b ≤ x.b → a.j ≤ x.j → order a ≤ order x)
    (horders : ∀ x, Valid x → InBox (r.plus x) (fullCap top) →
      order x = 1 ∨ availableMass r x (order x - 1) < layerNeed)
    (hprice : ∀ a, Valid a → InBox (r.plus a) (fullCap top) →
      physicalPrice a (order a) ≤ indexBudget r cap a.j) :
    Bellman top r cap := by
  let B := fun y : Shape => indexBudget r cap (49 - r.j - y.j)
  refine ⟨B, order, ?_, fun x hx hb => ⟨hpos x, horders x hx hb⟩, ?_⟩
  · change cap * (49 - r.j - 0) / (49 - r.j) ≤ cap
    rw [Nat.sub_zero]
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm])
  · intro y a _ ha hbox
    let x := y.plus a
    have hb : InBox (r.plus a) (fullCap top) :=
      ⟨(Nat.add_le_add_left (Nat.le_add_left a.b y.b) _).trans hbox.1,
        (Nat.add_le_add_left (Nat.le_add_left a.j y.j) _).trans hbox.2.1,
        (Nat.add_le_add_left (Nat.le_add_left a.t y.t) _).trans hbox.2.2⟩
    have hl := hmono (a := a) (x := x) (Nat.le_add_left _ _) (Nat.le_add_left _ _)
    have hfee := (physicalPrice_anti a (hpos a) hl).trans (hprice a ha hb)
    have hidx : r.j + (y.j + a.j) ≤ 49 := hbox.2.1
    have hbalance : a.j + (49 - r.j - x.j) = 49 - r.j - y.j := by
      change a.j + (49 - r.j - (y.j + a.j)) = 49 - r.j - y.j
      omega
    apply (Nat.add_le_add_right hfee (B x)).trans
    have hdiv : cap * a.j / (49 - r.j) + cap * (49 - r.j - x.j) / (49 - r.j) ≤
        (cap * a.j + cap * (49 - r.j - x.j)) / (49 - r.j) :=
      Nat.div_add_div_le_add_div
    rw [← Nat.mul_add, hbalance] at hdiv
    exact hdiv

private theorem ledger (top : ℕ) (htop : top ≤ 13) (k : Band) : Bellman top (start k) (factorCap top - reserve k) := by
  apply bellman_of_budget top _ _ (Low48PriceCaps.order k) (Low48PriceCaps.order_pos k)
    (Low48PriceCaps.order_mono k) (fun x _ _ => Low48PriceMass.order_valid k x) (Low48PriceTable.price top htop k)

private theorem retainedBox_down {a r : Shape} (h : InBox a r) (hr : Box r) :
    Box a := by
  rcases h with ⟨hb, hj, _⟩
  rcases hr with ⟨hrb, hrj, h4, h5, h6, h7⟩
  exact ⟨hb.trans hrb, hj.trans hrj, fun k => hb.trans (h4 (k.trans hj)),
    fun k => hb.trans (h5 (k.trans hj)), fun k => hb.trans (h6 (k.trans hj)), fun k => hb.trans (h7 (k.trans hj))⟩
private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} (hretained : Low48PriceReserve.Charges) (ha : ∀ i, Valid (a i)) (hbox : Box (P3_6_8.shapeSum a z))
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
    (hphys : ∀ i, 0 < l i → cost i ≤ physicalPrice (a i) (l i))
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
  have account : ∃ (q : Shape) (cap : ℕ), InBox q r ∧ (q = zeroShape ∨ 0 < q.j) ∧
      Bellman top q cap ∧ (∑ i ∈ z, cost i) + cap ≤ factorCap top := by
    rcases Low48PriceRetained.no_cut_shape a l ha hlayers z hz with hempty | ⟨hret, htr, htmax⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨zeroShape, factorCap top, ?_, Or.inl rfl, ledger top htop .empty, ?_⟩
      · rw [hr0]
        exact ⟨le_rfl, le_rfl, le_rfl⟩
      · simp [hempty]
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
      have hcost := retained_cost Low48PriceReserve.proof ha hret ht hfat
      rcases ht with ht | ht
      · refine ⟨oneStart, factorCap top - oneReserve, ?_, Or.inr (by decide), ledger top htop .one, ?_⟩
        · change 1 ≤ r.b ∧ 3 ≤ r.j ∧ 1 ≤ r.t
          omega
        · rw [ite_eq_left ht] at hcost
          exact (Nat.add_le_add_right hcost _).trans (by interval_cases top <;> decide)
      · refine ⟨twoStart, factorCap top - twoReserve, ?_, Or.inr (by decide), ledger top htop .two, ?_⟩
        · change 2 ≤ r.b ∧ 6 ≤ r.j ∧ 2 ≤ r.t
          omega
        · rw [ite_eq_right (by omega : r.t ≠ 1)] at hcost
          exact (Nat.add_le_add_right hcost _).trans (by interval_cases top <;> decide)
  obtain ⟨q, cap, hqr, hq, ⟨B, order, hB0, horder, hB⟩, haccount⟩ := account
  have hall : InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top) := hfits.2
  have hcap {s : Finset (Fin n)} (hs : s ⊆ pos) : InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top) := by
    have hb := P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _,
        Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have positive_bound (s : Finset (Fin n)) : s ⊆ pos →
      (∑ i ∈ s, cost i) + B (P3_6_8.shapeSum a s) ≤ B zeroShape := by
    refine Finset.strongInductionOn s fun s ih hs => ?_
    by_cases he : s.Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s l he
      let t := s.erase i
      have hti : i ∉ t := Finset.notMem_erase i s
      have hin : insert i t = s := Finset.insert_erase hi
      have hts : t ⊆ s := Finset.erase_subset i s
      have hprev := ih t (Finset.erase_ssubset hi) (hts.trans hs)
      have hvalid : P3_6_8.shapeSum a t = zeroShape ∨ Valid (P3_6_8.shapeSum a t) := by
        rcases P3_6_8.shapeSum_valid_or_empty ha t with ht | ht
        · exact Or.inl (ht ▸ P3_6_8.shapeSum_empty a)
        · exact Or.inr ht
      have hsvalid : Valid (P3_6_8.shapeSum a s) := by
        rcases P3_6_8.shapeSum_valid_or_empty ha s with hempty | hv
        · exact (he.ne_empty hempty).elim
        · exact hv
      have hL : 0 < l i := hpos i (hs hi)
      have hj : 0 < q.j + (P3_6_8.shapeSum a s).j := by
        obtain ⟨ht, hidx, _⟩ := hsvalid
        omega
      have hmass : layerNeed ≤ availableMass q (P3_6_8.shapeSum a s) (l i) :=
        (Low48PriceRetained.mass_le hlayers hz hmax (hdisj hs) hqr).trans (Low48PriceRetained.layerSum_le_available hq hj)
      have hc := hcap hs
      obtain ⟨horderPos, horderTest⟩ := horder _ hsvalid hc
      have hord : order (P3_6_8.shapeSum a s) ≤ l i := by
        rcases horderTest with heq | htest
        · omega
        · by_contra! h
          have hmono : availableMass q (P3_6_8.shapeSum a s) (l i) ≤
              availableMass q (P3_6_8.shapeSum a s) (order (P3_6_8.shapeSum a s) - 1) :=
            K1_13_8.availableMass_mono symbol_count hq hj (by omega)
          exact (not_lt_of_ge (hmass.trans hmono)) htest
      have hstep : physicalPrice (a i) (l i) + B (P3_6_8.shapeSum a s) ≤ B (P3_6_8.shapeSum a t) := by
        have hshape : P3_6_8.shapeSum a s = (P3_6_8.shapeSum a t).plus (a i) :=
          hin ▸ P3_6_8.shapeSum_insert a hti
        refine (Nat.add_le_add_right (physicalPrice_anti _ horderPos hord) _).trans ?_
        rw [hshape] at hc ⊢
        exact hB _ _ hvalid (ha i) hc
      have hfee := hphys i hL
      rw [← hin, Finset.sum_insert hti, hin]
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp he, P3_6_8.shapeSum_empty]
  have hpaid := positive_bound pos (Finset.Subset.rfl)
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap top
  omega

#print axioms total
end Low48PriceTotal

import ProximityPrize.SubmissionLower.Low48Price

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low48PriceRetained
open K1_13 (Shape InBox remaining)
open K1_13_8 (Valid zeroShape zeroMass layerTerm availableMass)
open P0_9_8 (symbol_count)
open Low48Price (layerNeed)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8


abbrev layerCount : ℕ := 1 + Low48Price.primaryCutoff / Low48Price.layerWidth

def Box (a : Shape) : Prop :=
  a.b ≤ 23 ∧ a.j ≤ 7 ∧ (4 ≤ a.j → a.b ≤ 21) ∧ (5 ≤ a.j → a.b ≤ 17) ∧
  (6 ≤ a.j → a.b ≤ 13) ∧ (7 ≤ a.j → a.b ≤ 6)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

private theorem reject3 : zeroMass 24 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 24) (j := 3) (m := 167) (by decide) (Or.inl (by decide))]
  decide +kernel

private theorem reject4 : zeroMass 22 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 22) (j := 4) (m := 182) (by decide) (Or.inl (by decide))]
  decide +kernel

private theorem reject5 : zeroMass 18 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 18) (j := 5) (m := 222) (by decide) (Or.inl (by decide))]
  decide +kernel

private theorem reject6 : zeroMass 14 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 14) (j := 6) (m := 275) (by decide) (Or.inr (by decide))]
  decide +kernel

private theorem reject7 : zeroMass 7 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 7) (j := 7) (m := 235) (by decide) (Or.inr (by decide))]
  decide +kernel

private theorem reject8 : zeroMass 3 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 8) (m := 206) (by decide) (Or.inr (by decide))]
  decide +kernel

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : Low48Price.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    Low48Price.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti ?_ ?_)
  · exact P3_6_8.spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact P3_6_8.spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
theorem layerSum_le_available {r y : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j) :
    (∑ k ∈ Finset.range layerCount, layerTerm r y L k) ≤ availableMass r y L := by
  let N := max layerCount (L + 1650 / (r.j + y.j))
  rw [← K1_13_8.availableMass_eq_sum symbol_count hr hj (N := N) (le_max_right _ _)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left _ _))

private theorem zeroMass_upper {b j : ℕ} (hj : 0 < j) :
    (∑ k ∈ Finset.range layerCount, remaining ((k + 1) * b) ((k + 1) * j)) ≤
      zeroMass b j := by
  unfold zeroMass
  simp only [symbol_count]
  rw [K1_13_8.sum_range_min layerCount (1650 / j)
    (fun k hk => K1_13_8.fastRemaining_zero (K1_13_8.index_over hj hk))]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))

private theorem retained_bound {r : Shape} (hr : Valid r)
    (hmass : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      remaining ((k + 1) * r.b) ((k + 1) * r.j)) : Box r := by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall : zeroMass b j < layerNeed) : False := by
    have hle : layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (zeroMass_upper hjpos)
    exact (not_lt_of_ge hle) hsmall
  obtain ⟨ht, hjt, hjb⟩ := hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject3
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject8
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject4
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject5
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject6
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject7

/-- The factors that receive no proper cut have total top degree at most two. -/
theorem no_cut_shape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i, Valid (a i)) (hl : Low48Price.LayerBudget a l)
    (z : Finset (Fin n)) (hz : ∀ i ∈ z, l i = 0) :
    z = ∅ ∨ (Box (combined a z) ∧ 1 ≤ (combined a z).t ∧ (combined a z).t ≤ 2) := by
  rcases P3_6_8.shapeSum_valid_or_empty ha z with h | hr
  · exact Or.inl h
  · right
    let r := P3_6_8.shapeSum a z
    have hb := mass_le hl (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
      (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
    have hbox : Box r := retained_bound hr (by
      simpa only [layerTerm, P3_6_8.shapeSum_empty, zeroShape, Nat.mul_zero, Nat.add_zero] using hb)
    refine ⟨hbox, hr.1, ?_⟩
    have hjet := hr.2.1
    have hj := hbox.2.1
    change 3*r.t ≤ r.j at hjet
    change (r.t ≤ 2)
    omega

#print axioms no_cut_shape
end Low48PriceRetained

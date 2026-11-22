import ProximityPrize.SubmissionLower.Low53At2389PriceLayer

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low53At2389PriceRetained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)
open Low53At2389Price (layerNeed)
open Low53At2389PriceLayer (layerTerm layerCount)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.mass_eq
  from ProximityPrize.SubmissionLower.GoldBranch6N8


def Box (a : Shape) : Prop :=
  a.b ≤ 25 ∧ a.j ≤ 7 ∧ (4 ≤ a.j → a.b ≤ 23) ∧ (5 ≤ a.j → a.b ≤ 20) ∧
  (6 ≤ a.j → a.b ≤ 16) ∧ (7 ≤ a.j → a.b ≤ 10)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

private theorem reject3 : zeroMass 26 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 26) (j := 3) (m := 154) (by decide) (Or.inl (by decide))]
  exact Low53At2389PriceLayer.sumBelow_lt _ _ [4506050141484, 3812811581688, 3185519361108, 2620295355264, 2113371734460, 1661090963784, 1259905803108, 906379307088, 597192602880, 331204292460, 124526225160, 18692802809, 359753742] (by decide +kernel) (by decide)

private theorem reject4 : zeroMass 24 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 24) (j := 4) (m := 167) (by decide) (Or.inl (by decide))]
  exact Low53At2389PriceLayer.sumBelow_lt _ _ [4476356057428, 3742512922900, 3093125074388, 2521872455572, 2022670349908, 1589669380628, 1217255510740, 900050043028, 632909620052, 410926274903, 229845417098, 92176891290, 16117023622, 397884432] (by decide +kernel) (by decide)

private theorem reject5 : zeroMass 21 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 21) (j := 5) (m := 191) (by decide) (Or.inl (by decide))]
  exact Low53At2389PriceLayer.sumBelow_lt _ _ [4455575555053, 3694361080189, 3031552375565, 2458516453981, 1967008264237, 1549170691133, 1197534555469, 905018614045, 664929559661, 470962021117, 317198563213, 198109686749, 108569233531, 44858537933, 8753391031, 222134352] (by decide +kernel) (by decide)

private theorem reject6 : zeroMass 17 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 17) (j := 6) (m := 236) (by decide) (Or.inl (by decide))]
  exact Low53At2389PriceLayer.sumBelow_lt _ _ [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 490662629132, 348260798444, 239109867788, 157622065772, 98720224268, 57837778412, 30918766604, 14417830508, 5300216092, 1072865524, 17811081] (by decide +kernel) (by decide)

private theorem reject7 : zeroMass 11 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 11) (j := 7) (m := 235) (by decide) (Or.inr rfl)]
  exact Low53At2389PriceLayer.sumBelow_lt _ _ [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 489103498308, 344309389864, 233448642084, 151010801208, 91928756068, 51578738088, 25780321284, 10796422264, 3333300228, 540556968, 12214020] (by decide +kernel) (by decide)

private theorem reject8 : zeroMass 3 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 8) (m := 206) (by decide) (Or.inr rfl)]
  exact Low53At2389PriceLayer.sumBelow_lt _ _ [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 643843537086, 447490661422, 295602473118, 182579293710, 102764821630, 50446132206, 19853677662, 5161287118, 486166590, 240929] (by decide +kernel) (by decide)

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : Low53At2389Price.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    Low53At2389Price.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => Low53At2389PriceLayer.remaining_anti ?_ ?_)
  · exact P3_6_8.spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact P3_6_8.spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
private theorem zeroMass_upper {b j : ℕ} (hj : 0 < j) :
    (∑ k ∈ Finset.range layerCount, K1_13.remaining ((k + 1) * b) ((k + 1) * j)) ≤
      zeroMass b j := by
  unfold zeroMass
  simp only [symbol_count]
  rw [K1_13_8.sum_range_min layerCount (1650 / j)
    (fun k hk => K1_13_8.fastRemaining_zero (K1_13_8.index_over hj hk))]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))

private theorem retained_bound {r : Shape} (hr : Valid r)
    (hmass : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      K1_13.remaining ((k + 1) * r.b) ((k + 1) * r.j)) : Box r := by
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
    (ha : ∀ i, Valid (a i)) (hl : Low53At2389Price.LayerBudget a l)
    (z : Finset (Fin n)) (hz : ∀ i ∈ z, l i = 0) :
    z = ∅ ∨ (Box (combined a z) ∧ 1 ≤ (combined a z).t ∧ (combined a z).t ≤ 2) := by
  rcases P3_6_8.shapeSum_valid_or_empty ha z with h | hr
  · exact Or.inl h
  · right
    let r := P3_6_8.shapeSum a z
    have hb := mass_le hl (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
      (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
    have hbox : Box r := retained_bound hr (by
      have hcost : layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm r zeroShape 0 k := by
        simpa only [P3_6_8.shapeSum_empty] using hb
      refine hcost.trans (Finset.sum_le_sum fun k _ => ?_)
      simp only [layerTerm, zeroShape, Nat.mul_zero, Nat.add_zero, Low53At2389Price.remaining]
      exact min_le_right _ _)
    refine ⟨hbox, hr.1, ?_⟩
    have hjet := hr.2.1
    have hj := hbox.2.1
    change 3*r.t ≤ r.j at hjet
    change (r.t ≤ 2)
    omega

#print axioms no_cut_shape
end Low53At2389PriceRetained

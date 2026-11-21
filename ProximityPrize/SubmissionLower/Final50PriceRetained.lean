import ProximityPrize.SubmissionLower.Final50PriceLayer

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Final50PriceRetained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)
open Final50Price (layerNeed)
open Final50PriceLayer (layerTerm layerCount)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8


def Box (a : Shape) : Prop :=
  a.b ≤ 25 ∧ a.j ≤ 7 ∧ (4 ≤ a.j → a.b ≤ 22) ∧ (5 ≤ a.j → a.b ≤ 19) ∧
  (6 ≤ a.j → a.b ≤ 15) ∧ (7 ≤ a.j → a.b ≤ 9)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 26 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 26) (j := 3) (m := 154) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 26 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,4506050141484,4506050141484
  have r2 := row! r1,12,24,3812811581688,8318861723172
  have r3 := row! r2,12,36,3185519361108,11504381084280
  have r4 := row! r3,12,48,2620295355264,14124676439544
  have r5 := row! r4,12,60,2113371734460,16238048174004
  have r6 := row! r5,12,72,1661090963784,17899139137788
  have r7 := row! r6,12,84,1259905803108,19159044940896
  have r8 := row! r7,12,96,906379307088,20065424247984
  have r9 := row! r8,12,108,597192602880,20662616850864
  have r10 := row! r9,12,120,331204292460,20993821143324
  have r11 := row! r10,12,132,124526225160,21118347368484
  have r12 := row! r11,12,144,18692802809,21137040171293
  have r13 := row! r12,10,154,359753742,21137399925035
  rw [r13]
  decide

private theorem reject4 : zeroMass 23 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 23) (j := 4) (m := 174) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 23 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4485571975228,4485571975228
  have r2 := row! r1,12,24,3766699705644,8252271680872
  have r3 := row! r2,12,36,3129542015772,11381813696644
  have r4 := row! r3,12,48,2568031469068,13949845165712
  have r5 := row! r4,12,60,2076325351932,16026170517644
  have r6 := row! r5,12,72,1648805673708,17674976191352
  have r7 := row! r6,12,84,1280079166684,18955055358036
  have r8 := row! r7,12,96,964977286092,19920032644128
  have r9 := row! r8,12,108,698556210108,20618588854236
  have r10 := row! r9,12,120,476096839852,21094685694088
  have r11 := row! r10,12,132,293125129224,21387810823312
  have r12 := row! r11,12,144,147129238370,21534940061682
  have r13 := row! r12,12,156,45704367459,21580644429141
  have r14 := row! r13,12,168,4426866335,21585071295476
  have r15 := row! r14,6,174,18369367,21585089664843
  rw [r15]
  decide

private theorem reject5 : zeroMass 20 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 20) (j := 5) (m := 200) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 20 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4464650819928,4464650819928
  have r2 := row! r1,12,24,3717680731508,8182331551436
  have r3 := row! r2,12,36,3065812876088,11248144427524
  have r4 := row! r3,12,48,2500800517668,13748944945192
  have r5 := row! r4,12,60,2014764120248,15763709065440
  have r6 := row! r5,12,72,1600191347828,17363900413268
  have r7 := row! r6,12,84,1249937064408,18613837477676
  have r8 := row! r7,12,96,957223333988,19571060811664
  have r9 := row! r8,12,108,715639420568,20286700232232
  have r10 := row! r9,12,120,519141788148,20805842020380
  have r11 := row! r10,12,132,362054100728,21167896121108
  have r12 := row! r11,12,144,239067222308,21406963343416
  have r13 := row! r12,12,156,145239216888,21552202560304
  have r14 := row! r13,12,168,76030644068,21628233204372
  have r15 := row! r14,12,180,28477980752,21656711185124
  have r16 := row! r15,12,192,4277265324,21660988450448
  have r17 := row! r16,8,200,49565740,21661038016188
  rw [r17]
  decide

private theorem reject6 : zeroMass 16 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 16) (j := 6) (m := 250) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 16 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4452236740149,4452236740149
  have r2 := row! r1,12,24,3688415547153,8140652287302
  have r3 := row! r2,12,36,3027292299789,11167944587091
  have r4 := row! r3,12,48,2459227806249,13627172393340
  have r5 := row! r4,12,60,1975057646181,15602230039521
  have r6 := row! r5,12,72,1566092170689,17168322210210
  have r7 := row! r6,12,84,1224116502333,18392438712543
  have r8 := row! r7,12,96,941390535129,19333829247672
  have r9 := row! r8,12,108,710648934549,20044478182221
  have r10 := row! r9,12,120,525101137521,20569579319742
  have r11 := row! r10,12,132,378431352429,20948010672171
  have r12 := row! r11,12,144,264798559113,21212809231284
  have r13 := row! r12,12,156,178836508869,21391645740153
  have r14 := row! r13,12,168,115653724449,21507299464602
  have r15 := row! r14,12,180,70833500061,21578132964663
  have r16 := row! r15,12,192,40433901369,21618566866032
  have r17 := row! r16,12,204,20987765493,21639554631525
  have r18 := row! r17,12,216,9502701009,21649057332534
  have r19 := row! r18,12,228,3461087949,21652518420483
  have r20 := row! r19,12,240,820143351,21653338563834
  have r21 := row! r20,10,250,46422905,21653384986739
  rw [r21]
  decide

private theorem reject7 : zeroMass 10 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 10) (j := 7) (m := 235) (by decide) (Or.inr rfl)]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 10 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4456729984713,4456729984713
  have r2 := row! r1,12,24,3698265082881,8154995067594
  have r3 := row! r2,12,36,3038986509241,11193981576835
  have r4 := row! r3,12,48,2470117587633,13664099164468
  have r5 := row! r4,12,60,1983268084905,15647367249373
  have r6 := row! r5,12,72,1570434210913,17217801460286
  have r7 := row! r6,12,84,1223998618521,18441800078807
  have r8 := row! r7,12,96,936730403601,19378530482408
  have r9 := row! r8,12,108,701785105033,20080315587441
  have r10 := row! r9,12,120,512704704705,20593020292146
  have r11 := row! r10,12,132,363417627513,20956437919659
  have r12 := row! r11,12,144,248238741361,21204676661020
  have r13 := row! r12,12,156,161869357161,21366546018181
  have r14 := row! r13,12,168,99397228833,21465943247014
  have r15 := row! r14,12,180,56296553305,21522239800319
  have r16 := row! r15,12,192,28427970513,21550667770832
  have r17 := row! r16,12,204,12038563401,21562706334233
  have r18 := row! r17,12,216,3761857921,21566468192154
  have r19 := row! r18,12,228,617823033,21567086015187
  have r20 := row! r19,7,235,14133535,21567100148722
  rw [r20]
  decide

private theorem reject8 : zeroMass 3 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 8) (m := 206) (by decide) (Or.inr rfl)]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 3 8) 0 = 0 := rfl
  have r1 := row! r0,12,12,4468671078718,4468671078718
  have r2 := row! r1,12,24,3721807051950,8190478130668
  have r3 := row! r2,12,36,3062166708510,11252644839178
  have r4 := row! r3,12,48,2484603354766,13737248193944
  have r5 := row! r4,12,60,1983913673982,15721161867926
  have r6 := row! r5,12,72,1554837726318,17275999594244
  have r7 := row! r6,12,84,1192058948830,18468058543074
  have r8 := row! r7,12,96,890204155470,19358262698544
  have r9 := row! r8,12,108,643843537086,20002106235630
  have r10 := row! r9,12,120,447490661422,20449596897052
  have r11 := row! r10,12,132,295602473118,20745199370170
  have r12 := row! r11,12,144,182579293710,20927778663880
  have r13 := row! r12,12,156,102764821630,21030543485510
  have r14 := row! r13,12,168,50446132206,21080989617716
  have r15 := row! r14,12,180,19853677662,21100843295378
  have r16 := row! r15,12,192,5161287118,21106004582496
  have r17 := row! r16,12,204,486166590,21106490749086
  have r18 := row! r17,2,206,240929,21106490990015
  rw [r18]
  decide

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : Final50Price.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    Final50Price.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => Final50PriceLayer.remaining_anti ?_ ?_)
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
    (ha : ∀ i, Valid (a i)) (hl : Final50Price.LayerBudget a l)
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
      simp only [layerTerm, zeroShape, Nat.mul_zero, Nat.add_zero, Final50Price.remaining]
      exact min_le_right _ _)
    refine ⟨hbox, hr.1, ?_⟩
    have hjet := hr.2.1
    have hj := hbox.2.1
    change 3*r.t ≤ r.j at hjet
    change (r.t ≤ 2)
    omega

#print axioms no_cut_shape
end Final50PriceRetained

import ProximityPrize.SubmissionLower.LowLayers82190

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace LowRetained82190
open K1_13 (Shape InBox remaining)
open K1_13_8 (Valid zeroShape zeroMass layerTerm layerCount)
open P0_9_8 (symbol_count)
open LowLayers82190 (layerNeed)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8

def Box (a : Shape) : Prop :=
  a.b ≤ 23 ∧ a.j ≤ 7 ∧ (4 ≤ a.j → a.b ≤ 20) ∧ (5 ≤ a.j → a.b ≤ 17) ∧
  (6 ≤ a.j → a.b ≤ 12) ∧ (7 ≤ a.j → a.b ≤ 5)

def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 24 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 24) (j := 3) (m := 167) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 24 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,4524766555282,4524766555282
  have r2 := row! r1,12,24,3862963391974,8387729947256
  have r3 := row! r2,12,36,3262846079770,11650576027026
  have r4 := row! r3,12,48,2720826787822,14371402814848
  have r5 := row! r4,12,60,2233419022114,16604821836962
  have r6 := row! r5,12,72,1797237625462,18402059462424
  have r7 := row! r6,12,84,1408998777514,19811058239938
  have r8 := row! r7,12,96,1065519994750,20876578234688
  have r9 := row! r8,12,108,763720130482,21640298365170
  have r10 := row! r9,12,120,500646774200,22140945139370
  have r11 := row! r10,12,132,275946015463,22416891154833
  have r12 := row! r11,12,144,103939662330,22520830817163
  have r13 := row! r12,12,156,16415639747,22537246456910
  have r14 := row! r13,11,167,397884432,22537644341342
  rw [r14]
  decide

private theorem reject4 : zeroMass 21 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 21) (j := 4) (m := 191) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 21 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4504003810828,4504003810828
  have r2 := row! r1,12,24,3815073271132,8319077081960
  have r3 := row! r2,12,36,3202375898540,11521452980500
  have r4 := row! r3,12,48,2660349496060,14181802476560
  have r5 := row! r4,12,60,2183635355980,16365437832540
  have r6 := row! r5,12,72,1767078259868,18132516092408
  have r7 := row! r6,12,84,1405726478572,19538242570980
  have r8 := row! r7,12,96,1094831772220,20633074343200
  have r9 := row! r8,12,108,829849390220,21462923733420
  have r10 := row! r9,12,120,606438071260,22069361804680
  have r11 := row! r10,12,132,420460043308,22489821847988
  have r12 := row! r11,12,144,267982918038,22757804766026
  have r13 := row! r12,12,156,145857337035,22903662103061
  have r14 := row! r13,12,168,56134739197,22959796842258
  have r15 := row! r14,12,180,9318556289,22969115398547
  have r16 := row! r15,11,191,222134352,22969337532899
  rw [r16]
  decide

private theorem reject5 : zeroMass 18 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 18) (j := 5) (m := 222) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 18 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4482801349678,4482801349678
  have r2 := row! r1,12,24,3764320034146,8247121383824
  have r3 := row! r2,12,36,3134333877134,11381455260958
  have r4 := row! r3,12,48,2585368645042,13966823906000
  have r5 := row! r4,12,60,2110275832270,16077099738270
  have r6 := row! r5,12,72,1702232661218,17779332399488
  have r7 := row! r6,12,84,1354742082286,19134074481774
  have r8 := row! r7,12,96,1061632773874,20195707255648
  have r9 := row! r8,12,108,817059142382,21012766398030
  have r10 := row! r9,12,120,615501322210,21628267720240
  have r11 := row! r10,12,132,451765175758,22080032895998
  have r12 := row! r11,12,144,320982293426,22401015189424
  have r13 := row! r12,12,156,218609993614,22619625183038
  have r14 := row! r13,12,168,140431322722,22760056505760
  have r15 := row! r14,12,180,82555055150,22842611560910
  have r16 := row! r15,12,192,41433740975,22884045301885
  have r17 := row! r16,12,204,14501106127,22898546408012
  have r18 := row! r17,12,216,1830981315,22900377389327
  have r19 := row! r18,6,222,10163916,22900387553243
  rw [r19]
  decide

private theorem reject6 : zeroMass 13 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 13) (j := 6) (m := 275) (by decide) (Or.inr rfl)]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 13 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4479045454224,4479045454224
  have r2 := row! r1,12,24,3755838228768,8234883682992
  have r3 := row! r2,12,36,3123868817520,11358752500512
  have r4 := row! r3,12,48,2575130055552,13933882556064
  have r5 := row! r4,12,60,2101982053968,16035864610032
  have r6 := row! r5,12,72,1697152199904,17733016809936
  have r7 := row! r6,12,84,1353735156528,19086751966464
  have r8 := row! r7,12,96,1065192863040,20151944829504
  have r9 := row! r8,12,108,825354534672,20977299364176
  have r10 := row! r9,12,120,628416662688,21605716026864
  have r11 := row! r10,12,132,468943014384,22074659041248
  have r12 := row! r11,12,144,341864633088,22416523674336
  have r13 := row! r12,12,156,242479838160,22659003512496
  have r14 := row! r13,12,168,166454224992,22825457737488
  have r15 := row! r14,12,180,109820665008,22935278402496
  have r16 := row! r15,12,192,68979305664,23004257708160
  have r17 := row! r16,12,204,40697570448,23044955278608
  have r18 := row! r17,12,216,22110158880,23067065437488
  have r19 := row! r18,12,228,10719046512,23077784484000
  have r20 := row! r19,12,240,4393484928,23082177968928
  have r21 := row! r20,12,252,1370001744,23083547970672
  have r22 := row! r21,12,264,252400608,23083800371280
  have r23 := row! r22,11,275,11761200,23083812132480
  rw [r23]
  decide

private theorem reject7 : zeroMass 6 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 6) (j := 7) (m := 235) (by decide) (Or.inr rfl)]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 6 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4491925293069,4491925293069
  have r2 := row! r1,12,24,3784865989109,8276791282178
  have r3 := row! r2,12,36,3159826881533,11436618163711
  have r4 := row! r3,12,48,2610926737893,14047544901604
  have r5 := row! r4,12,60,2132443170413,16179988072017
  have r6 := row! r5,12,72,1718812635989,17898800708006
  have r7 := row! r6,12,84,1364630436189,19263431144195
  have r8 := row! r7,12,96,1064650717253,20328081861448
  have r9 := row! r8,12,108,813786470093,21141868331541
  have r10 := row! r9,12,120,607109530293,21748977861834
  have r11 := row! r10,12,132,439850578109,22188828439943
  have r12 := row! r11,12,144,307399138469,22496227578412
  have r13 := row! r12,12,156,205303580973,22701531159385
  have r14 := row! r13,12,168,129271119893,22830802279278
  have r15 := row! r14,12,180,75167814173,22905970093451
  have r16 := row! r15,12,192,39018567429,22944988660880
  have r17 := row! r16,12,204,17007127949,22961995788829
  have r18 := row! r17,12,216,5476088693,22967471877522
  have r19 := row! r18,12,228,926887293,22968398764815
  have r20 := row! r19,7,235,21811595,22968420576410
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
    (hlayers : LowLayers82190.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    LowLayers82190.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  have hcount : 1 + LowLayers82190.primaryCutoff / LowLayers82190.layerWidth ≤ layerCount := by decide
  refine hlayers.trans ((Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti ?_ ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono hcount)))
  · exact P3_6_8.spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact P3_6_8.spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
private theorem retained_bound {r : Shape} (hr : Valid r)
    (hmass : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      remaining ((k + 1) * r.b) ((k + 1) * r.j)) : Box r := by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall : zeroMass b j < layerNeed) : False := by
    have hle : layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (K1_13_8.zeroMass_upper symbol_count hjpos)
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
    (ha : ∀ i, Valid (a i)) (hl : LowLayers82190.LayerBudget a l)
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
end LowRetained82190

import ProximityPrize.SubmissionLower.LowLayers82170

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace LowRetained82170
open K1_13 (Shape InBox remaining)
open K1_13_8 (Valid zeroShape zeroMass layerTerm layerCount)
open P0_9_8 (symbol_count)
open LowLayers82170 (layerNeed)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8


def Box (a : Shape) : Prop :=
  a.b ≤ 21 ∧ a.j ≤ 6 ∧ (4 ≤ a.j → a.b ≤ 18) ∧ (5 ≤ a.j → a.b ≤ 15) ∧ (6 ≤ a.j → a.b ≤ 9)

def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 22 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 22) (j := 3) (m := 182) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 22 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,4543482969080,4543482969080
  have r2 := row! r1,12,24,3913115202260,8456598171340
  have r3 := row! r2,12,36,3340172798432,11796770969772
  have r4 := row! r3,12,48,2821358220380,14618129190152
  have r5 := row! r4,12,60,2353466309768,16971595499920
  have r6 := row! r5,12,72,1933384287140,18904979787060
  have r7 := row! r6,12,84,1558091751920,20463071538980
  have r8 := row! r7,12,96,1224660682412,21687732221392
  have r9 := row! r8,12,108,930255435800,22617987657192
  have r10 := row! r9,12,120,672132748148,23290120405340
  have r11 := row! r10,12,132,447662064236,23737782469576
  have r12 := row! r11,12,144,256042691026,23993825160602
  have r13 := row! r12,12,156,106462974463,24100288135065
  have r14 := row! r13,12,168,21721978082,24122010113147
  have r15 := row! r14,12,180,1036878942,24123046992089
  have r16 := row! r15,2,182,46871,24123047038960
  rw [r16]
  decide

private theorem reject4 : zeroMass 19 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 19) (j := 4) (m := 211) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 19 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4522435646428,4522435646428
  have r2 := row! r1,12,24,3863446836620,8385882483048
  have r3 := row! r2,12,36,3275209781308,11661092264356
  have r4 := row! r3,12,48,2752667523052,14413759787408
  have r5 := row! r4,12,60,2290945360028,16704705147436
  have r6 := row! r5,12,72,1885350846028,18590055993464
  have r7 := row! r6,12,84,1531373790460,20121429783924
  have r8 := row! r7,12,96,1224686258348,21346116042272
  have r9 := row! r8,12,108,961142570332,22307258612604
  have r10 := row! r9,12,120,736779302668,23044037915272
  have r11 := row! r10,12,132,547815287228,23591853202500
  have r12 := row! r11,12,144,390651611500,23982504814000
  have r13 := row! r12,12,156,261871618588,24244376432588
  have r14 := row! r13,12,168,158276202812,24402652635400
  have r15 := row! r14,12,180,78057231412,24480709866812
  have r16 := row! r15,12,192,24237660443,24504947527255
  have r17 := row! r16,12,204,2519994877,24507467522132
  have r18 := row! r17,7,211,15381961,24507482904093
  rw [r18]
  decide

private theorem reject5 : zeroMass 16 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 16) (j := 5) (m := 250) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 16 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4500951879428,4500951879428
  have r2 := row! r1,12,24,3810959336784,8311911216212
  have r3 := row! r2,12,36,3202854878180,11514766094392
  have r4 := row! r3,12,48,2669936772416,14184702866808
  have r5 := row! r4,12,60,2205787544292,16390490411100
  have r6 := row! r5,12,72,1804273974608,18194764385708
  have r7 := row! r6,12,84,1459547100164,19654311485872
  have r8 := row! r7,12,96,1166042213760,20820353699632
  have r9 := row! r8,12,108,918478864196,21738832563828
  have r10 := row! r9,12,120,711860856272,22450693420100
  have r11 := row! r10,12,132,541476250788,22992169670888
  have r12 := row! r11,12,144,402897364544,23395067035432
  have r13 := row! r12,12,156,291980770340,23687047805772
  have r14 := row! r13,12,168,204867296976,23891915102748
  have r15 := row! r14,12,180,137982029252,24029897132000
  have r16 := row! r15,12,192,88034307968,24117931439968
  have r17 := row! r16,12,204,52017729924,24169949169892
  have r18 := row! r17,12,216,27210148960,24197159318852
  have r19 := row! r18,12,228,11204767902,24208364086754
  have r20 := row! r19,12,240,2426944294,24210791031048
  have r21 := row! r20,10,250,66122122,24210857153170
  rw [r21]
  decide

private theorem reject6 : zeroMass 10 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 10) (j := 6) (m := 275) (by decide) (Or.inr rfl)]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 10 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4505854168299,4505854168299
  have r2 := row! r1,12,24,3823260910383,8329115078682
  have r3 := row! r2,12,36,3220445335251,11549560413933
  have r4 := row! r3,12,48,2691032304855,14240592718788
  have r5 := row! r4,12,60,2228906461755,16469499180543
  have r6 := row! r5,12,72,1828212229119,18297711409662
  have r7 := row! r6,12,84,1483353810723,19781065220385
  have r8 := row! r7,12,96,1188995190951,20970060411336
  have r9 := row! r8,12,108,940060134795,21910120546131
  have r10 := row! r9,12,120,731732187855,22641852733986
  have r11 := row! r10,12,132,559454676339,23201307410325
  have r12 := row! r11,12,144,418930707063,23620238117388
  have r13 := row! r12,12,156,306123167451,23926361284839
  have r14 := row! r13,12,168,217254725535,24143616010374
  have r15 := row! r14,12,180,148807829955,24292423840329
  have r16 := row! r15,12,192,97524709959,24389948550288
  have r17 := row! r16,12,204,60407375403,24450355925691
  have r18 := row! r17,12,216,34717616751,24485073542442
  have r19 := row! r18,12,228,17977005075,24503050547517
  have r20 := row! r19,12,240,7966892055,24511017439572
  have r21 := row! r20,12,252,2728409979,24513745849551
  have r22 := row! r21,12,264,562471743,24514308321294
  have r23 := row! r22,11,275,29770851,24514338092145
  rw [r23]
  decide

private theorem reject7 : zeroMass 3 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 7) (m := 235) (by decide) (Or.inr rfl)]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 3 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4518321774336,4518321774336
  have r2 := row! r1,12,24,3849816668780,8368138443116
  have r3 := row! r2,12,36,3250457160752,11618595603868
  have r4 := row! r3,12,48,2716533600588,14335129204456
  have r5 := row! r4,12,60,2244324484544,16579453689000
  have r6 := row! r5,12,72,1830096454796,18409550143796
  have r7 := row! r6,12,84,1470104299440,19879654443236
  have r8 := row! r7,12,96,1160590952492,21040245395728
  have r9 := row! r8,12,108,897787493888,21938032889616
  have r10 := row! r9,12,120,677913149484,22615946039100
  have r11 := row! r10,12,132,497175291056,23113121330156
  have r12 := row! r11,12,144,351769436300,23464890766456
  have r13 := row! r12,12,156,237879248832,23702770015288
  have r14 := row! r13,12,168,151676538188,23854446553476
  have r15 := row! r14,12,180,89321259824,23943767813300
  have r16 := row! r15,12,192,46961515116,23990729328416
  have r17 := row! r16,12,204,20733551360,24011462879776
  have r18 := row! r17,12,216,6761761772,24018224641548
  have r19 := row! r18,12,228,1158685488,24019383327036
  have r20 := row! r19,7,235,27570140,24019410897176
  rw [r20]
  decide

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : LowLayers82170.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    LowLayers82170.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  have hcount : 1 + LowLayers82170.primaryCutoff / LowLayers82170.layerWidth ≤ layerCount := by decide
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject3
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject4
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject5
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject6

/-- The factors that receive no proper cut have total top degree at most two. -/
theorem no_cut_shape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i, Valid (a i)) (hl : LowLayers82170.LayerBudget a l)
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
end LowRetained82170

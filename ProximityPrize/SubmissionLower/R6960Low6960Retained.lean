import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.R6960Low6960Order

-- merged module Final50PriceLayer
section Merged_Final50PriceLayer

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Final50PriceLayer
open K1_13 (Shape)
open K1_13_8 (zeroShape zeroMass fastRemaining)
open Final50Price (remaining symbolCount)
open P0_9_8 (symbol_count)
open scoped BigOperators

abbrev layerCount : ℕ := 1 + Final50Price.primaryCutoff / Final50Price.layerWidth

def layerTerm (r y : Shape) (L i : ℕ) : ℕ :=
  remaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)

def fastLayer (r y : Shape) (L i : ℕ) : ℕ :=
  if r.j = 0 ∧ i < L then symbolCount else
    fastRemaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)

def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  if r.j = 0 then L * symbolCount + zeroMass y.b y.j
  else K1_13_8.availableMass r y L

theorem remaining_anti {b j b' j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') :
    remaining b' j' ≤ remaining b j :=
  min_le_min_left _ (K1_13_8.remaining_anti hb hj)

private theorem layerTerm_le (r y : Shape) (L i : ℕ) : layerTerm r y L i ≤ fastLayer r y L i := by
  unfold layerTerm fastLayer remaining
  split
  · exact min_le_left _ _
  · rw [← symbol_count]
    exact min_le_right _ _

theorem availableMass_eq_sum {r y : Shape} {L N : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) (hN : L + 1650 / (r.j + y.j) ≤ N) :
    (∑ i ∈ Finset.range N, fastLayer r y L i) = availableMass r y L := by
  rcases hr with rfl | hp
  · simp only [zeroShape, Nat.zero_add] at hj hN
    have hL := (Nat.le_add_right L (1650 / y.j)).trans hN
    rw [← Nat.add_sub_of_le hL, Finset.sum_range_add]
    have hfirst : (∑ i ∈ Finset.range L, fastLayer zeroShape y L i) = L * symbolCount := by
      calc
        _ = ∑ _i ∈ Finset.range L, symbolCount := Finset.sum_congr rfl fun i hi => by
          simp [fastLayer, zeroShape, Finset.mem_range.mp hi]
        _ = _ := by simp
    have htail (i : ℕ) : fastLayer zeroShape y L (L+i) =
        fastRemaining ((i+1)*y.b) ((i+1)*y.j) := by
      have hi : ¬ L+i < L := by omega
      have hi' : L+i+1-L = i+1 := by omega
      simp [fastLayer, zeroShape, hi, hi']
    rw [hfirst]
    simp_rw [htail]
    rw [K1_13_8.sum_range_truncate (m := 1650/y.j)
      (fun i hi => K1_13_8.fastRemaining_zero (K1_13_8.index_over hj hi)) (by omega)]
    rfl
  · rw [availableMass, ite_eq_right hp.ne']
    rw [← K1_13_8.availableMass_eq_sum symbol_count (Or.inr hp) hj hN]
    simp [fastLayer, K1_13_8.layerTerm, symbol_count, hp.ne']

theorem layerSum_le_available {r y : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j) :
    (∑ k ∈ Finset.range layerCount, layerTerm r y L k) ≤ availableMass r y L := by
  let N := max layerCount (L + 1650 / (r.j + y.j))
  rw [← availableMass_eq_sum hr hj (N := N) (le_max_right _ _)]
  exact K1_13_8.sum_range_mono (le_max_left _ _) fun k _ => layerTerm_le r y L k

theorem availableMass_mono {r y : Shape} {l u : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) (hl : l ≤ u) : availableMass r y l ≤ availableMass r y u := by
  rcases hr with rfl | hp
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right symbolCount hl) _
  · simp only [availableMass, ite_eq_right hp.ne']
    exact K1_13_8.availableMass_mono symbol_count (Or.inr hp) hj hl

theorem availableMass_anti_prefix {r y x : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j+y.j)
    (hb : y.b ≤ x.b) (hidx : y.j ≤ x.j) : availableMass r x L ≤ availableMass r y L := by
  rcases hr with rfl | hp
  · have h := P0_9_8.availableMass_anti_prefix (L := 0) (Or.inl rfl : zeroShape = zeroShape ∨ 0 < zeroShape.j) hj hb hidx
    have hz (a : Shape) : K1_13_8.availableMass zeroShape a 0 = zeroMass a.b a.j := by
      simp [K1_13_8.availableMass, zeroShape, zeroMass]
    rw [hz, hz] at h
    exact Nat.add_le_add_left h _
  · simp only [availableMass, ite_eq_right hp.ne']
    exact P0_9_8.availableMass_anti_prefix (Or.inr hp) hj hb hidx
end Final50PriceLayer

end Merged_Final50PriceLayer

-- merged module R6960Low6960Retained
section Merged_R6960Low6960Retained

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low6960Retained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)
open Lower6960.Low (layerCount)
local notation "layerNeed" => Lower6960.Low.need
open Final50PriceLayer (layerTerm)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty spend_le)
open P3_6_8_1 (sumBelow term mass_eq extend)


def Box (a : Shape) : Prop :=
  a.b ≤ 27 ∧ a.j ≤ 8 ∧ (4 ≤ a.j → a.b ≤ 25) ∧ (5 ≤ a.j → a.b ≤ 22) ∧
  (6 ≤ a.j → a.b ≤ 19) ∧ (7 ≤ a.j → a.b ≤ 14) ∧ (8 ≤ a.j → a.b ≤ 6)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 28 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 28) (j := 3) (m := 143) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 28 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,4487333727686,4487333727686
  have r2 := row! r1,12,24,3762659771402,8249993499088
  have r3 := row! r2,12,36,3108192642446,11358186141534
  have r4 := row! r3,12,48,2519763922706,13877950064240
  have r5 := row! r4,12,60,1993324446806,15871274511046
  have r6 := row! r5,12,72,1524944302106,17396218813152
  have r7 := row! r6,12,84,1110812828702,18507031641854
  have r8 := row! r7,12,96,747238668280,19254270310134
  have r9 := row! r8,12,108,431539940145,19685810250279
  have r10 := row! r9,12,120,176240195865,19862050446144
  have r11 := row! r10,12,132,30699448338,19892749894482
  have r12 := row! r11,11,143,773590642,19893523485124
  rw [r12]
  decide

private theorem reject4 : zeroMass 26 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 26) (j := 4) (m := 154) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 26 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4457924221828,4457924221828
  have r2 := row! r1,12,24,3694139357412,8152063579240
  have r3 := row! r2,12,36,3020291191620,11172354770860
  have r4 := row! r3,12,48,2429554428580,13601909199440
  have r5 := row! r4,12,60,1915360345860,15517269545300
  have r6 := row! r5,12,72,1471396794468,16988666339768
  have r7 := row! r6,12,84,1091608198852,18080274538620
  have r8 := row! r7,12,96,770195556900,18850470095520
  have r9 := row! r8,12,108,501616440976,19352086536496
  have r10 := row! r9,12,120,280971568492,19633058104988
  have r11 := row! r10,12,132,111555751260,19744613856248
  have r12 := row! r11,12,144,18384312204,19762998168452
  have r13 := row! r12,10,154,359753742,19763357922194
  rw [r13]
  decide

private theorem reject5 : zeroMass 23 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 23) (j := 5) (m := 174) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 23 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4437425025303,4437425025303
  have r2 := row! r1,12,24,3647721777551,8085146802854
  have r3 := row! r2,12,36,2963031374519,11048178177373
  have r4 := row! r3,12,48,2373948326607,13422126503980
  have r5 := row! r4,12,60,1871496552215,15293623056195
  have r6 := row! r5,12,72,1447129377743,16740752433938
  have r7 := row! r6,12,84,1092729537591,17833481971529
  have r8 := row! r7,12,96,800609174159,18634091145688
  have r9 := row! r8,12,108,563509837847,19197600983535
  have r10 := row! r9,12,120,374602487055,19572203470590
  have r11 := row! r10,12,132,227487489219,19799690959809
  have r12 := row! r11,12,144,116378050133,19916069009942
  have r13 := row! r12,12,156,39557489286,19955626499228
  have r14 := row! r13,12,168,4378437247,19960004936475
  have r15 := row! r14,6,174,18369367,19960023305842
  rw [r15]
  decide

private theorem reject6 : zeroMass 20 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 20) (j := 6) (m := 200) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 20 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4416491788049,4416491788049
  have r2 := row! r1,12,24,3598518638333,8015010426382
  have r3 := row! r2,12,36,2898523609481,10913534035863
  have r4 := row! r3,12,48,2304691473845,13218225509708
  have r5 := row! r4,12,60,1805825102465,15024050612173
  have r6 := row! r5,12,72,1391345465069,16415396077242
  have r7 := row! r6,12,84,1051291630073,17466687707315
  have r8 := row! r7,12,96,776320764581,18243008471896
  have r9 := row! r8,12,108,557708134385,18800716606281
  have r10 := row! r9,12,120,387347103965,19188063710246
  have r11 := row! r10,12,132,257749136489,19445812846735
  have r12 := row! r11,12,144,162043793813,19607856640548
  have r13 := row! r12,12,156,93978736481,19701835377029
  have r14 := row! r13,12,168,47919723725,19749755100754
  have r15 := row! r14,12,180,18887896997,19768642997751
  have r16 := row! r15,12,192,3562975968,19772205973719
  have r17 := row! r16,8,200,49565740,19772255539459
  rw [r17]
  decide

private theorem reject7 : zeroMass 15 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 15) (j := 7) (m := 235) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 15 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4412735849268,4412735849268
  have r2 := row! r1,12,24,3590013950096,8002749799364
  have r3 := row! r2,12,36,2887936043876,10890685843240
  have r4 := row! r3,12,48,2294106149808,13184791993048
  have r5 := row! r4,12,60,1796799228020,14981591221068
  have r6 := row! r5,12,72,1384961179568,16366552400636
  have r7 := row! r6,12,84,1048208846436,17414761247072
  have r8 := row! r7,12,96,776830011536,18191591258608
  have r9 := row! r8,12,108,561783398708,18753374657316
  have r10 := row! r9,12,120,394698672720,19148073330036
  have r11 := row! r10,12,132,267876439268,19415949769304
  have r12 := row! r11,12,144,174288244976,19590238014280
  have r13 := row! r12,12,156,107576577396,19697814591676
  have r14 := row! r13,12,168,62054865008,19759869456684
  have r15 := row! r14,12,180,32707477220,19792576933904
  have r16 := row! r15,12,192,15189724368,19807766658272
  have r17 := row! r16,12,204,5827857716,19813594515988
  have r18 := row! r17,12,216,1619069456,19815213585444
  have r19 := row! r18,12,228,231492708,19815445078152
  have r20 := row! r19,7,235,4535960,19815449614112
  rw [r20]
  decide

private theorem reject8 : zeroMass 7 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 7) (j := 8) (m := 206) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 7 8) 0 = 0 := rfl
  have r1 := row! r0,12,12,4434018990758,4434018990758
  have r2 := row! r1,12,24,3638417588822,8072436579580
  have r3 := row! r2,12,36,2948917116678,11021353696258
  have r4 := row! r3,12,48,2356675780790,13378029477048
  have r5 := row! r4,12,60,1853134903142,15231164380190
  have r6 := row! r5,12,72,1430018921238,16661183301428
  have r7 := row! r6,12,84,1079335388102,17740518689530
  have r8 := row! r7,12,96,793374972278,18533893661808
  have r9 := row! r8,12,108,564711457830,19098605119638
  have r10 := row! r9,12,120,386201744342,19484806863980
  have r11 := row! r10,12,132,250985846918,19735792710898
  have r12 := row! r11,12,144,152486896182,19888279607080
  have r13 := row! r12,12,156,84411138278,19972690745358
  have r14 := row! r13,12,168,40747934870,20013438680228
  have r15 := row! r14,12,180,15769763142,20029208443370
  have r16 := row! r15,12,192,4032215798,20033240659168
  have r17 := row! r16,12,204,374001062,20033614660230
  have r18 := row! r17,2,206,182693,20033614842923
  rw [r18]
  decide

private theorem reject9 : zeroMass 3 9 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 9) (m := 183) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 3 9) 0 = 0 := rfl
  have r1 := row! r0,12,12,4419454632432,4419454632432
  have r2 := row! r1,12,24,3596534841372,8015989473804
  have r3 := row! r2,12,36,2880841206984,10896830680788
  have r4 := row! r3,12,48,2265453291444,13162283972232
  have r5 := row! r4,12,60,1743314608032,14905598580264
  have r6 := row! r5,12,72,1307232621132,16212831201396
  have r7 := row! r6,12,84,949878746232,17162709947628
  have r8 := row! r7,12,96,663788349924,17826498297552
  have r9 := row! r8,12,108,441360749904,18267859047456
  have r10 := row! r9,12,120,274859214972,18542718262428
  have r11 := row! r10,12,132,156410965032,18699129227460
  have r12 := row! r11,12,144,78007171092,18777136398552
  have r13 := row! r12,12,156,31502955264,18808639353816
  have r14 := row! r13,12,168,8617390764,18817256744580
  have r15 := row! r14,12,180,933501912,18818190246492
  have r16 := row! r15,3,183,1782176,18818192028668
  rw [r16]
  decide

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : Lower6960.Low.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    Lower6960.Low.need ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject3
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject9
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject4
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject5
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject6
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject8

/-- The factors that receive no proper cut have total top degree at most two. -/
theorem no_cut_shape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i, Valid (a i)) (hl : Lower6960.Low.LayerBudget a l)
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
end Low6960Retained

end Merged_R6960Low6960Retained

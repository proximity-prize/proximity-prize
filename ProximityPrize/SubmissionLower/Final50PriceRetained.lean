import ProximityPrize.SubmissionLower.Final50Price

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
  a.b ≤ 25 ∧ a.j ≤ 7 ∧ (4 ≤ a.j → a.b ≤ 23) ∧ (5 ≤ a.j → a.b ≤ 20) ∧
  (6 ≤ a.j → a.b ≤ 16) ∧ (7 ≤ a.j → a.b ≤ 10)
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

private theorem reject4 : zeroMass 24 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 24) (j := 4) (m := 167) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 24 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4476356057428,4476356057428
  have r2 := row! r1,12,24,3742512922900,8218868980328
  have r3 := row! r2,12,36,3093125074388,11311994054716
  have r4 := row! r3,12,48,2521872455572,13833866510288
  have r5 := row! r4,12,60,2022670349908,15856536860196
  have r6 := row! r5,12,72,1589669380628,17446206240824
  have r7 := row! r6,12,84,1217255510740,18663461751564
  have r8 := row! r7,12,96,900050043028,19563511794592
  have r9 := row! r8,12,108,632909620052,20196421414644
  have r10 := row! r9,12,120,410926274903,20607347689547
  have r11 := row! r10,12,132,229845417098,20837193106645
  have r12 := row! r11,12,144,92176891290,20929369997935
  have r13 := row! r12,12,156,16117023622,20945487021557
  have r14 := row! r13,11,167,397884432,20945884905989
  rw [r14]
  decide

private theorem reject5 : zeroMass 21 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 21) (j := 5) (m := 191) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 21 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4455575555053,4455575555053
  have r2 := row! r1,12,24,3694361080189,8149936635242
  have r3 := row! r2,12,36,3031552375565,11181489010807
  have r4 := row! r3,12,48,2458516453981,13640005464788
  have r5 := row! r4,12,60,1967008264237,15607013729025
  have r6 := row! r5,12,72,1549170691133,17156184420158
  have r7 := row! r6,12,84,1197534555469,18353718975627
  have r8 := row! r7,12,96,905018614045,19258737589672
  have r9 := row! r8,12,108,664929559661,19923667149333
  have r10 := row! r9,12,120,470962021117,20394629170450
  have r11 := row! r10,12,132,317198563213,20711827733663
  have r12 := row! r11,12,144,198109686749,20909937420412
  have r13 := row! r12,12,156,108569233531,21018506653943
  have r14 := row! r13,12,168,44858537933,21063365191876
  have r15 := row! r14,12,180,8753391031,21072118582907
  have r16 := row! r15,11,191,222134352,21072340717259
  rw [r16]
  decide

private theorem reject6 : zeroMass 17 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 17) (j := 6) (m := 236) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 17 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4443300502124,4443300502124
  have r2 := row! r1,12,24,3665941319948,8109241822072
  have r3 := row! r2,12,36,2995100127212,11104341949284
  have r4 := row! r3,12,48,2420593723148,13524935672432
  have r5 := row! r4,12,60,1932749510252,15457685182684
  have r6 := row! r5,12,72,1522405494284,16980090676968
  have r7 := row! r6,12,84,1180910284268,18161000961236
  have r8 := row! r7,12,96,900123092492,19061124053728
  have r9 := row! r8,12,108,672413734508,19733537788236
  have r10 := row! r9,12,120,490662629132,20224200417368
  have r11 := row! r10,12,132,348260798444,20572461215812
  have r12 := row! r11,12,144,239109867788,20811571083600
  have r13 := row! r12,12,156,157622065772,20969193149372
  have r14 := row! r13,12,168,98720224268,21067913373640
  have r15 := row! r14,12,180,57837778412,21125751152052
  have r16 := row! r15,12,192,30918766604,21156669918656
  have r17 := row! r16,12,204,14417830508,21171087749164
  have r18 := row! r17,12,216,5300216092,21176387965256
  have r19 := row! r18,12,228,1072865524,21177460830780
  have r20 := row! r19,8,236,17811081,21177478641861
  rw [r20]
  decide

private theorem reject7 : zeroMass 11 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 11) (j := 7) (m := 235) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 11 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4447931157624,4447931157624
  have r2 := row! r1,12,24,3676614856324,8124546013948
  have r3 := row! r2,12,36,3008776416168,11133322430116
  have r4 := row! r3,12,48,2434915300068,13568237730184
  have r5 := row! r4,12,60,1945974313528,15514212043712
  have r6 := row! r5,12,72,1533339604644,17047551648356
  have r7 := row! r6,12,84,1188840664104,18236392312460
  have r8 := row! r7,12,96,904750325188,19141142637648
  have r9 := row! r8,12,108,673784763768,19814927401416
  have r10 := row! r9,12,120,489103498308,20304030899724
  have r11 := row! r10,12,132,344309389864,20648340289588
  have r12 := row! r11,12,144,233448642084,20881788931672
  have r13 := row! r12,12,156,151010801208,21032799732880
  have r14 := row! r13,12,168,91928756068,21124728488948
  have r15 := row! r14,12,180,51578738088,21176307227036
  have r16 := row! r15,12,192,25780321284,21202087548320
  have r17 := row! r16,12,204,10796422264,21212883970584
  have r18 := row! r17,12,216,3333300228,21216217270812
  have r19 := row! r18,12,228,540556968,21216757827780
  have r20 := row! r19,7,235,12214020,21216770041800
  rw [r20]
  decide

private theorem reject8 : zeroMass 3 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 8) (m := 206) (by decide) (Or.inr (by decide))]
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
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
  a.b ≤ 26 ∧ a.j ≤ 8 ∧ (4 ≤ a.j → a.b ≤ 24) ∧ (5 ≤ a.j → a.b ≤ 21) ∧
  (6 ≤ a.j → a.b ≤ 18) ∧ (7 ≤ a.j → a.b ≤ 12) ∧ (8 ≤ a.j → a.b ≤ 4)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 27 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 27) (j := 3) (m := 148) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 27 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,4496691934585,4496691934585
  have r2 := row! r1,12,24,3787735676545,8284427611130
  have r3 := row! r2,12,36,3146856001777,11431283612907
  have r4 := row! r3,12,48,2570029638985,14001313251892
  have r5 := row! r4,12,60,2053348090633,16054661342525
  have r6 := row! r5,12,72,1593017632945,17647678975470
  have r7 := row! r6,12,84,1185359315905,18833038291375
  have r8 := row! r7,12,96,826808963257,19659847254632
  have r9 := row! r8,12,108,514063060931,20173910315563
  have r10 := row! r9,12,120,250519872085,20424430187648
  have r11 := row! r10,12,132,68168387085,20492598574733
  have r12 := row! r11,12,144,4897672803,20497496247536
  have r13 := row! r12,4,148,5416761,20497501664297
  rw [r13]
  decide

private theorem reject4 : zeroMass 25 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 25) (j := 4) (m := 160) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 25 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4467140139628,4467140139628
  have r2 := row! r1,12,24,3718326140156,8185466279784
  have r3 := row! r2,12,36,3056708133004,11242174412788
  have r4 := row! r3,12,48,2475713442076,13717887854864
  have r5 := row! r4,12,60,1969015347884,15686903202748
  have r6 := row! r5,12,72,1530533087548,17217436290296
  have r7 := row! r6,12,84,1154431854796,18371868145092
  have r8 := row! r7,12,96,835122799964,19206990945056
  have r9 := row! r8,12,108,567263029996,19774253975052
  have r10 := row! r9,12,120,345783007790,20120036982842
  have r11 := row! r10,12,132,168356316089,20288393298931
  have r12 := row! r11,12,144,47413035334,20335806334265
  have r13 := row! r12,12,156,3484477592,20339290811857
  have r14 := row! r13,4,160,3496480,20339294308337
  rw [r14]
  decide

private theorem reject5 : zeroMass 22 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 22) (j := 5) (m := 182) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 22 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4446500290178,4446500290178
  have r2 := row! r1,12,24,3671041428870,8117541719048
  have r3 := row! r2,12,36,2997291875042,11114833594090
  have r4 := row! r3,12,48,2416232390294,13531065984384
  have r5 := row! r4,12,60,1919252408226,15450318392610
  have r6 := row! r5,12,72,1498150034438,16948468427048
  have r7 := row! r6,12,84,1145132046530,18093600473578
  have r8 := row! r7,12,96,852813894102,18946414367680
  have r9 := row! r8,12,108,614219698754,19560634066434
  have r10 := row! r9,12,120,422782254086,19983416320520
  have r11 := row! r10,12,132,272343025698,20255759346218
  have r12 := row! r11,12,144,157154045616,20412913391834
  have r13 := row! r12,12,156,72455558497,20485368950331
  have r14 := row! r13,12,168,18878847395,20504247797726
  have r15 := row! r14,12,180,1036779119,20505284576845
  have r16 := row! r15,2,182,46871,20505284623716
  rw [r16]
  decide

private theorem reject6 : zeroMass 19 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 19) (j := 6) (m := 211) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 19 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4425428026074,4425428026074
  have r2 := row! r1,12,24,3620992865538,8046420891612
  have r3 := row! r2,12,36,2930715782058,10977136673670
  have r4 := row! r3,12,48,2343325556946,13320462230616
  have r5 := row! r4,12,60,1848133238394,15168595469010
  have r6 := row! r5,12,72,1435032141474,16603627610484
  have r7 := row! r6,12,84,1094497848138,17698125458622
  have r8 := row! r7,12,96,817588207218,18515713665840
  have r9 := row! r8,12,108,595943334426,19111657000266
  have r10 := row! r9,12,120,421785612354,19533442612620
  have r11 := row! r10,12,132,287919690474,19821362303094
  have r12 := row! r11,12,144,187732485138,20009094788232
  have r13 := row! r12,12,156,115193179578,20124287967810
  have r14 := row! r13,12,168,64853223906,20189141191716
  have r15 := row! r14,12,180,31846335114,20220987526830
  have r16 := row! r15,12,192,11906544751,20232894071581
  have r17 := row! r16,12,204,1997023009,20234891094590
  have r18 := row! r17,7,211,15381961,20234906476551
  rw [r18]
  decide

private theorem reject7 : zeroMass 13 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 13) (j := 7) (m := 235) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 13 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4430333503446,4430333503446
  have r2 := row! r1,12,24,3633314403210,8063647906656
  have r3 := row! r2,12,36,2948356230022,11012004136678
  have r4 := row! r3,12,48,2364510724938,13376514861616
  have r5 := row! r4,12,60,1871386770774,15247901632390
  have r6 := row! r5,12,72,1459150392106,16707052024496
  have r7 := row! r6,12,84,1118524755270,17825576779766
  have r8 := row! r7,12,96,840790168362,18666366948128
  have r9 := row! r8,12,108,617784081238,19284151029366
  have r10 := row! r9,12,120,441901085514,19726052114880
  have r11 := row! r10,12,132,306092914566,20032145029446
  have r12 := row! r11,12,144,203868443530,20236013472976
  have r13 := row! r12,12,156,129293689302,20365307162278
  have r14 := row! r13,12,168,76991810538,20442298972816
  have r15 := row! r14,12,180,42143107654,20484442080470
  have r16 := row! r15,12,192,20485022826,20504927103296
  have r17 := row! r16,12,204,8312139990,20513239243286
  have r18 := row! r17,12,216,2476184842,20515715428128
  have r19 := row! r18,12,228,386024838,20516101452966
  have r20 := row! r19,7,235,8374990,20516109827956
  rw [r20]
  decide

private theorem reject8 : zeroMass 5 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 5) (j := 8) (m := 206) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 5 8) 0 = 0 := rfl
  have r1 := row! r0,12,12,4451345034738,4451345034738
  have r2 := row! r1,12,24,3680112320386,8131457355124
  have r3 := row! r2,12,36,3005541912594,11136999267718
  have r4 := row! r3,12,48,2420639567778,13557638835496
  have r5 := row! r4,12,60,1918524288562,15476163124058
  have r6 := row! r5,12,72,1492428323778,16968591447836
  have r7 := row! r6,12,84,1135697168466,18104288616302
  have r8 := row! r7,12,96,841789563874,18946078180176
  have r9 := row! r8,12,108,604277497458,19550355677634
  have r10 := row! r9,12,120,416846202882,19967201880516
  have r11 := row! r10,12,132,273294160018,20240496040534
  have r12 := row! r11,12,144,167533094946,20408029135480
  have r13 := row! r12,12,156,93587979954,20501617115434
  have r14 := row! r13,12,168,45597033538,20547214148972
  have r15 := row! r14,12,180,17811720402,20565025869374
  have r16 := row! r15,12,192,4596751458,20569622620832
  have r17 := row! r16,12,204,430083826,20570052704658
  have r18 := row! r17,2,206,211811,20570052916469
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

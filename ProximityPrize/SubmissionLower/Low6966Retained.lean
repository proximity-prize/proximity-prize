import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.R6960Low6960Retained

section Merged6967_Low6966Retained
set_option Elab.async false




set_option Elab.async false

namespace Final50PriceLayer
open K1_13 (Shape)
open K1_13_8 (zeroShape zeroMass fastRemaining)
open Final50Price (remaining symbolCount)
open P0_9_8 (symbol_count)
open scoped BigOperators

private theorem extra_term_le (r y : Shape) (L i : ℕ) : layerTerm r y L i ≤ fastLayer r y L i := by
  unfold layerTerm fastLayer remaining
  split
  · exact min_le_left _ _
  · rw [← symbol_count]
    exact min_le_right _ _

theorem layerSum_le_available_n {r y : Shape} {L : ℕ} (n : ℕ)
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j) :
    (∑ k ∈ Finset.range n, layerTerm r y L k) ≤ availableMass r y L := by
  let N := max n (L + 1650 / (r.j + y.j))
  rw [← availableMass_eq_sum hr hj (N := N) (le_max_right _ _)]
  exact K1_13_8.sum_range_mono (le_max_left _ _) fun k _ => extra_term_le r y L k

end Final50PriceLayer


-- merged module R6960Low6966Retained
section Merged_R6960Low6966Retained

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low6966Retained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)
open LowProfile6966 (layerCount)
local notation "layerNeed" => LowProfile6966.need
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
    (hlayers : LowProfile6966.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    LowProfile6966.need ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
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
    (ha : ∀ i, Valid (a i)) (hl : LowProfile6966.LayerBudget a l)
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
end Low6966Retained

end Merged_R6960Low6966Retained

end Merged6967_Low6966Retained

section Merged6967_Low6966SharedRational
set_option Elab.async false



set_option Elab.async false
set_option maxHeartbeats 800000
namespace Low6966SharedRational
noncomputable section

open K1_13 (Geom Row)
open K1_13_3 (symbolAt)
open K1_13_6 (GenericField GeoField genericCoeffs toGeneric)
open Polynomial MvPolynomial
open scoped BigOperators nonZeroDivisors

abbrev FractionJet := MvPolynomial (Fin 4) GenericField

def toFraction (P : Row 4) : FractionJet :=
  MvPolynomial.map (algebraMap (Polynomial Geom) GenericField) P

def toGeometric : FractionJet →+* K1_13_6.GeoJets :=
  MvPolynomial.map (algebraMap GenericField GeoField)

theorem fraction_geometric (P : Row 4) :
    toGeometric (toFraction P) = toGeneric P := by
  simp [toGeometric,toFraction,toGeneric,genericCoeffs,MvPolynomial.map_map]

theorem fraction_injective : Function.Injective toFraction :=
  MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Geom) _)

theorem support_fraction (P : Row 4) : (toFraction P).support = P.support :=
  MvPolynomial.support_map_of_injective P (IsFractionRing.injective (Polynomial Geom) GenericField)

private theorem primitive_relation {ι : Type*} (s : Finset ι) (c : ι → (Polynomial Geom))
    (e : ι → Row 4) (h : ∑ i ∈ s, c i • e i = 0)
    (hne : ∃ i ∈ s, c i ≠ 0) (x : Geom) :
    ∃ b : ι → (Polynomial Geom), (∑ i ∈ s, b i • e i = 0) ∧ ∃ i ∈ s, (b i).eval x ≠ 0 := by
  classical
  let S := s.filter fun i => c i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hc⟩ := hne
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hc⟩⟩
  obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => (c i).rootMultiplicity x) hS
  let k := (c i).rootMultiplicity x
  let D : (Polynomial Geom) := (Polynomial.X - Polynomial.C x)^k
  have hd : D ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
  have hdiv (j : ι) : D ∣ c j ∨ j ∉ s := by
    by_cases hzero : c j = 0
    · exact Or.inl (hzero.symm ▸ dvd_zero D)
    · by_cases hs : j ∈ s
      · exact Or.inl ((pow_dvd_pow _ (hmin j (Finset.mem_filter.mpr ⟨hs,hzero⟩))).trans
          (Polynomial.pow_rootMultiplicity_dvd _ _))
      · exact Or.inr hs
  have hclear (j : ι) : ∃ b : (Polynomial Geom), j ∈ s → c j = D*b := by
    rcases hdiv j with ⟨b,hb⟩ | hno
    · exact ⟨b,fun _ => hb⟩
    · exact ⟨0,fun hyes => (hno hyes).elim⟩
  choose b hb using hclear
  have hii := Finset.mem_filter.mp hi
  have hsum : D • (∑ j ∈ s, b j • e j) = 0 := by
    rw [Finset.smul_sum]
    refine (Finset.sum_congr rfl fun j hj => ?_).trans h
    rw [smul_smul,← hb j hj]
  have hz : ∑ j ∈ s, b j • e j = 0 := (smul_eq_zero.mp hsum).resolve_left hd
  refine ⟨b,hz,i,hii.1,?_⟩
  intro he
  obtain ⟨P,hP⟩ := (Polynomial.dvd_iff_isRoot).mpr he
  have hnot : ¬ (Polynomial.X - Polynomial.C x)^(k+1) ∣ c i :=
    Polynomial.pow_rootMultiplicity_not_dvd hii.2 x
  apply hnot
  refine ⟨P, ?_⟩
  calc
    c i = D * b i := hb i hii.1
    _ = _ := by rw [hP]; dsimp only [D]; rw [pow_succ,mul_assoc]


/-- Specialization independence implies function-field independence. -/
theorem independent_fraction {ι : Type*} (x : Geom) (e : ι → Row 4)
    (he : LinearIndependent Geom (fun i => symbolAt x (e i))) :
    LinearIndependent GenericField (fun i => toFraction (e i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  let R := (Polynomial Geom)
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples (R⁰) s a
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hc (j : ι) : ∃ c : R, j ∈ s →
      algebraMap R GenericField c = algebraMap R GenericField d * a j := by
    by_cases hm : j ∈ s
    · obtain ⟨c,hc⟩ := hd j hm
      exact ⟨c,fun _ => hc.trans (Algebra.smul_def _ _)⟩
    · exact ⟨0,fun hj => (hm hj).elim⟩
  choose c hc using hc
  have hcleared : ∑ j ∈ s, c j • e j = 0 := by
    apply fraction_injective
    unfold toFraction
    simp only [map_sum,map_zero]
    calc
      _ = ∑ j ∈ s, (algebraMap R GenericField d * a j) •
          MvPolynomial.map (algebraMap R GenericField) (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have heq := hc j hj
        change algebraMap (Polynomial Geom) GenericField (c j) = _ at heq
        simp only [← MvPolynomial.C_mul', map_mul,MvPolynomial.map_C,heq]
        rw [mul_assoc]
      _ = (algebraMap R GenericField d) • ∑ j ∈ s, a j • toFraction (e j) := by
        rw [Finset.smul_sum]
        simp only [smul_smul, toFraction]
        rfl
      _ = 0 := by rw [ha,smul_zero]
  by_contra ha0
  have hc0 : c i ≠ 0 := by
    intro hz
    have heC := hc i hi
    rw [hz,map_zero] at heC
    have hNZ : algebraMap R GenericField d ≠ 0 := fun hz =>
      hd0 (IsFractionRing.injective R GenericField (hz.trans (map_zero _).symm))
    exact (mul_ne_zero hNZ ha0) heC.symm
  obtain ⟨b,hb,j,hj,hjx⟩ := primitive_relation s c e hcleared ⟨i,hi,hc0⟩ x
  have hx : ∑ j ∈ s, (b j).eval x • symbolAt x (e j) = 0 := by
    have hs := congrArg (symbolAt x) hb
    simp only [map_sum,map_zero,← MvPolynomial.C_mul',map_mul] at hs
    change (∑ j ∈ s, (evalRingHom x) (b j) • symbolAt x (e j)) = 0
    simpa only [symbolAt, MvPolynomial.map_C, MvPolynomial.C_mul'] using hs
  exact hjx (linearIndependent_iff'.mp he s (fun j => (b j).eval x) hx j hj)

theorem clear_denominators (R : FractionJet) :
    ∃ (d : (Polynomial Geom)) (Q : Row 4), d ≠ 0 ∧ Q.support = R.support ∧
      toFraction Q = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField d) * R := by
  classical
  let M := nonZeroDivisors ((Polynomial Geom))
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 4 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : (Polynomial Geom)) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : algebraMap (Polynomial Geom) GenericField (d : (Polynomial Geom)) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericField)).mpr hd
  have hQ : toFraction Q = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField d) * R := by
    unfold toFraction
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change algebraMap (Polynomial Geom) GenericField (num a) = (d : (Polynomial Geom)) • R.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [MvPolynomial.coeff_monomial, hb]
    · have hz : R.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (MvPolynomial.monomial a.val (num a) : Row 4).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [MvPolynomial.coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, Q, hd, ?_, hQ⟩
  rw [← support_fraction Q, hQ]
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hi]

#print axioms clear_denominators
#print axioms independent_fraction
end
end Low6966SharedRational

end Merged6967_Low6966SharedRational

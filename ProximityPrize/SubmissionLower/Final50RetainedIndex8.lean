import ProximityPrize.SubmissionLower.Final50PriceRetained

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Final50RetainedIndex8
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open Final50Price (layerNeed)
open Final50PriceLayer (layerTerm layerCount)
open Final50PriceRetained (combined mass_le)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8
open private Final50PriceRetained.reject3 Final50PriceRetained.reject4
  Final50PriceRetained.reject5 Final50PriceRetained.reject6 Final50PriceRetained.reject7
  Final50PriceRetained.zeroMass_upper from ProximityPrize.SubmissionLower.Final50PriceRetained

def Box (a : Shape) : Prop :=
  a.b≤26 ∧ a.j≤8 ∧ (4≤a.j→a.b≤24) ∧ (5≤a.j→a.b≤21) ∧
  (6≤a.j→a.b≤17) ∧ (7≤a.j→a.b≤12) ∧ (8≤a.j→a.b≤3)

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n:=len) (N:=nxt) (y:=v) (total:=z) h rfl rfl rfl

private theorem reject8 : zeroMass 4 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=4) (j:=8) (m:=206) (by decide) (Or.inr (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 4 8) 0=0:=rfl
  have r1:=row! r0,12,12,4460008056728,4460008056728
  have r2:=row! r1,12,24,3700959686168,8160967742896
  have r3:=row! r2,12,36,3033854310552,11194822053448
  have r4:=row! r3,12,48,2452621461272,13647443514720
  have r5:=row! r4,12,60,1951218981272,15598662495992
  have r6:=row! r5,12,72,1523633025048,17122295521040
  have r7:=row! r6,12,84,1163878058648,18286173579688
  have r8:=row! r7,12,96,865996859672,19152170439360
  have r9:=row! r8,12,108,624060517272,19776230956632
  have r10:=row! r9,12,120,432168432152,20208399388784
  have r11:=row! r10,12,132,284448316568,20492847705352
  have r12:=row! r11,12,144,175056194328,20667903899680
  have r13:=row! r12,12,156,98176400792,20766080300472
  have r14:=row! r13,12,168,48021582872,20814101883344
  have r15:=row! r14,12,180,18832699032,20832934582376
  have r16:=row! r15,12,192,4879019288,20837813601664
  have r17:=row! r16,12,204,458125208,20838271726872
  have r18:=row! r17,2,206,226370,20838271953242
  rw [r18]
  decide

private theorem reject9 : zeroMass 3 9 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=3) (j:=9) (m:=183) (by decide) (Or.inr (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 3 9) 0=0:=rfl
  have r1:=row! r0,12,12,4419454632432,4419454632432
  have r2:=row! r1,12,24,3596534841372,8015989473804
  have r3:=row! r2,12,36,2880841206984,10896830680788
  have r4:=row! r3,12,48,2265453291444,13162283972232
  have r5:=row! r4,12,60,1743314608032,14905598580264
  have r6:=row! r5,12,72,1307232621132,16212831201396
  have r7:=row! r6,12,84,949878746232,17162709947628
  have r8:=row! r7,12,96,663788349924,17826498297552
  have r9:=row! r8,12,108,441360749904,18267859047456
  have r10:=row! r9,12,120,274859214972,18542718262428
  have r11:=row! r10,12,132,156410965032,18699129227460
  have r12:=row! r11,12,144,78007171092,18777136398552
  have r13:=row! r12,12,156,31502955264,18808639353816
  have r14:=row! r13,12,168,8617390764,18817256744580
  have r15:=row! r14,12,180,933501912,18818190246492
  have r16:=row! r15,3,183,1782176,18818192028668
  rw [r16]
  decide

private theorem retained_bound {r : Shape} (hr : Valid r)
    (hmass : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      K1_13.remaining ((k+1)*r.b) ((k+1)*r.j)):Box r:=by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall:zeroMass b j < layerNeed):False:=by
    have hle : layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (Final50PriceRetained.zeroMass_upper hjpos)
    exact (not_lt_of_ge hle) hsmall
  obtain ⟨ht,hjt,hjb⟩:=hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) Final50PriceRetained.reject3
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject9
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) Final50PriceRetained.reject4
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) Final50PriceRetained.reject5
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) Final50PriceRetained.reject6
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) Final50PriceRetained.reject7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject8

/-- The factors that receive no proper cut have total top degree at most two. -/
theorem no_cut_shape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i,Valid (a i)) (hl:Final50Price.LayerBudget a l)
    (z:Finset (Fin n)) (hz : ∀ i ∈ z,l i=0) :
    z = ∅ ∨ (Box (combined a z) ∧ 1≤(combined a z).t ∧ (combined a z).t≤2):=by
  rcases P3_6_8.shapeSum_valid_or_empty ha z with h | hr
  · exact Or.inl h
  · right
    let r:=P3_6_8.shapeSum a z
    have hb := mass_le hl (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
      (show InBox r r from ⟨le_rfl,le_rfl,le_rfl⟩)
    have hbox : Box r := retained_bound hr (by
      have hcost : layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm r zeroShape 0 k := by
        simpa only [P3_6_8.shapeSum_empty] using hb
      refine hcost.trans (Finset.sum_le_sum fun k _ => ?_)
      simp only [layerTerm,zeroShape,Nat.mul_zero,Nat.add_zero,Final50Price.remaining]
      exact min_le_right _ _)
    refine ⟨hbox,hr.1, ?_⟩
    have hjet:=hr.2.1
    have hj:=hbox.2.1
    change 3*r.t≤r.j at hjet
    change (r.t≤2)
    omega

#print axioms no_cut_shape
end Final50RetainedIndex8

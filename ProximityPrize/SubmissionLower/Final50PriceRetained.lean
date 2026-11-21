import ProximityPrize.SubmissionLower.Final50PriceLayer

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Final50PriceRetained
open K1_13 (Shape InBox remaining)
open K1_13_8 (Valid zeroShape zeroMass)
open Final50PriceLayer (layerTerm layerCount)
open P0_9_8 (symbol_count)
open Final50Price (layerNeed)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8



def Box (a : Shape) : Prop :=
  a.b ≤ 23 ∧ a.j ≤ 7 ∧ (4 ≤ a.j → a.b ≤ 21) ∧ (5 ≤ a.j → a.b ≤ 18) ∧
  (6 ≤ a.j → a.b ≤ 13) ∧ (7 ≤ a.j → a.b ≤ 6)
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

private theorem reject4 : zeroMass 22 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 22) (j := 4) (m := 182) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 22 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4494787893028,4494787893028
  have r2 := row! r1,12,24,3790886488388,8285674381416
  have r3 := row! r2,12,36,3165958957156,11451633338572
  have r4 := row! r3,12,48,2614190482564,14065823821136
  have r5 := row! r4,12,60,2129980353956,16195804175092
  have r6 := row! r5,12,72,1707941966788,17903746141880
  have r7 := row! r6,12,84,1342902822628,19246648964508
  have r8 := row! r7,12,96,1029904529156,20276553493664
  have r9 := row! r8,12,108,764202800164,21040756293828
  have r10 := row! r9,12,120,541267455556,21582023749384
  have r11 := row! r10,12,132,356782422384,21938806171768
  have r12 := row! r11,12,144,206829164170,22145635335938
  have r13 := row! r12,12,156,91343958058,22236979293996
  have r14 := row! r13,12,168,20893146940,22257872440936
  have r15 := row! r14,12,180,1036878942,22258909319878
  have r16 := row! r15,2,182,46871,22258909366749
  rw [r16]
  decide

private theorem reject5 : zeroMass 19 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 19) (j := 5) (m := 211) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 19 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4473726084803,4473726084803
  have r2 := row! r1,12,24,3741000382827,8214726467630
  have r3 := row! r2,12,36,3100073376611,11314799844241
  have r4 := row! r3,12,48,2543084581355,13857884425596
  have r5 := row! r4,12,60,2062519976259,15920404401855
  have r6 := row! r5,12,72,1651212004523,17571616406378
  have r7 := row! r6,12,84,1302339573347,18873955979725
  have r8 := row! r7,12,96,1009428053931,19883384033656
  have r9 := row! r8,12,108,766349281475,20649733315131
  have r10 := row! r9,12,120,567321555179,21217054870310
  have r11 := row! r10,12,132,406909638243,21623964508553
  have r12 := row! r11,12,144,280024757867,21903989266420
  have r13 := row! r12,12,156,181924605251,22085913871671
  have r14 := row! r13,12,168,108213335595,22194127207266
  have r15 := row! r14,12,180,54878851631,22249006058897
  have r16 := row! r15,12,192,19304284391,22268310343288
  have r17 := row! r16,12,204,2452448089,22270762791377
  have r18 := row! r17,7,211,15381961,22270778173338
  rw [r18]
  decide

private theorem reject6 : zeroMass 14 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 14) (j := 6) (m := 275) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 14 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4470109216199,4470109216199
  have r2 := row! r1,12,24,3733364001563,8203473217762
  have r3 := row! r2,12,36,3091676644943,11295149862705
  have r4 := row! r3,12,48,2536495972451,13831645835156
  have r5 := row! r4,12,60,2059673918039,15891319753195
  have r6 := row! r5,12,72,1653465523499,17544785276694
  have r7 := row! r6,12,84,1310528938463,18855314215157
  have r8 := row! r7,12,96,1023925420403,19879239635560
  have r9 := row! r8,12,108,787119334631,20666358970191
  have r10 := row! r9,12,120,593978154299,21260337124490
  have r11 := row! r10,12,132,438772460399,21699109584889
  have r12 := row! r11,12,144,316175941763,22015285526652
  have r13 := row! r12,12,156,221265395063,22236550921715
  have r14 := row! r13,12,168,149520724811,22386071646526
  have r15 := row! r14,12,180,96824943359,22482896589885
  have r16 := row! r15,12,192,59464170899,22542360760784
  have r17 := row! r16,12,204,34127635463,22576488396247
  have r18 := row! r17,12,216,17907672923,22594396069170
  have r19 := row! r18,12,228,8299726991,22602695796161
  have r20 := row! r19,12,240,3202349219,22605898145380
  have r21 := row! r20,12,252,917198999,22606815344379
  have r22 := row! r21,12,264,149043563,22606964387942
  have r23 := row! r22,11,275,5757983,22606970145925
  rw [r23]
  decide

private theorem reject7 : zeroMass 7 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 7) (j := 7) (m := 235) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 7 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4483126465980,4483126465980
  have r2 := row! r1,12,24,3763215762552,8246342228532
  have r3 := row! r2,12,36,3129616788460,11375959016992
  have r4 := row! r3,12,48,2575724450328,13951683467320
  have r5 := row! r4,12,60,2095149399036,16046832866356
  have r6 := row! r5,12,72,1681718029720,17728550896076
  have r7 := row! r6,12,84,1329472481772,19058023377848
  have r8 := row! r7,12,96,1032670638840,20090694016688
  have r9 := row! r8,12,108,785786128828,20876480145516
  have r10 := row! r9,12,120,583508323896,21459988469412
  have r11 := row! r10,12,132,420742340460,21880730809872
  have r12 := row! r11,12,144,292609039192,22173339849064
  have r13 := row! r12,12,156,194445025020,22367784874084
  have r14 := row! r13,12,168,121802647128,22489587521212
  have r15 := row! r14,12,180,70449998956,22560037520168
  have r16 := row! r15,12,192,36370918200,22596408438368
  have r17 := row! r16,12,204,15764986812,22612173425180
  have r18 := row! r17,12,216,5047531000,22617220956180
  have r19 := row! r18,12,228,849621228,22618070577408
  have r20 := row! r19,7,235,19892080,22618090469488
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
    (ha : ∀ i, Valid (a i)) (hl : Final50Price.LayerBudget a l)
    (z : Finset (Fin n)) (hz : ∀ i ∈ z, l i = 0) :
    z = ∅ ∨ (Box (combined a z) ∧ 1 ≤ (combined a z).t ∧ (combined a z).t ≤ 2) := by
  rcases P3_6_8.shapeSum_valid_or_empty ha z with h | hr
  · exact Or.inl h
  · right
    let r := P3_6_8.shapeSum a z
    have hb := mass_le hl (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
      (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
    have hp : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
        Final50Price.remaining ((k + 1) * r.b) ((k + 1) * r.j) := by
      simpa only [layerTerm, P3_6_8.shapeSum_empty, zeroShape, Nat.mul_zero, Nat.add_zero] using hb
    have hbox : Box r := retained_bound hr (hp.trans (Finset.sum_le_sum fun _ _ => min_le_right _ _))
    refine ⟨hbox, hr.1, ?_⟩
    have hjet := hr.2.1
    have hj := hbox.2.1
    change 3*r.t ≤ r.j at hjet
    change (r.t ≤ 2)
    omega

#print axioms no_cut_shape
end Final50PriceRetained

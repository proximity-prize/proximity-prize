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
  a.b≤26 ∧ a.j≤7 ∧ (4≤a.j→a.b≤24) ∧ (5≤a.j→a.b≤21) ∧
  (6≤a.j→a.b≤17) ∧ (7≤a.j→a.b≤12)
def combined {n:ℕ} (a:Fin n→Shape) (z:Finset (Fin n)):=P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n:=len) (N:=nxt) (y:=v) (total:=z) h rfl rfl rfl

private theorem reject3 : zeroMass 27 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=27) (j:=3) (m:=148) (by decide) (Or.inl (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 27 3) 0=0:=rfl
  have r1:=row! r0,12,12,4496691934585,4496691934585
  have r2:=row! r1,12,24,3787735676545,8284427611130
  have r3:=row! r2,12,36,3146856001777,11431283612907
  have r4:=row! r3,12,48,2570029638985,14001313251892
  have r5:=row! r4,12,60,2053348090633,16054661342525
  have r6:=row! r5,12,72,1593017632945,17647678975470
  have r7:=row! r6,12,84,1185359315905,18833038291375
  have r8:=row! r7,12,96,826808963257,19659847254632
  have r9:=row! r8,12,108,514063060931,20173910315563
  have r10:=row! r9,12,120,250519872085,20424430187648
  have r11:=row! r10,12,132,68168387085,20492598574733
  have r12:=row! r11,12,144,4897672803,20497496247536
  have r13:=row! r12,4,148,5416761,20497501664297
  rw [r13]
  decide

private theorem reject4 : zeroMass 25 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=25) (j:=4) (m:=160) (by decide) (Or.inl (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 25 4) 0=0:=rfl
  have r1:=row! r0,12,12,4467140139628,4467140139628
  have r2:=row! r1,12,24,3718326140156,8185466279784
  have r3:=row! r2,12,36,3056708133004,11242174412788
  have r4:=row! r3,12,48,2475713442076,13717887854864
  have r5:=row! r4,12,60,1969015347884,15686903202748
  have r6:=row! r5,12,72,1530533087548,17217436290296
  have r7:=row! r6,12,84,1154431854796,18371868145092
  have r8:=row! r7,12,96,835122799964,19206990945056
  have r9:=row! r8,12,108,567263029996,19774253975052
  have r10:=row! r9,12,120,345783007790,20120036982842
  have r11:=row! r10,12,132,168356316089,20288393298931
  have r12:=row! r11,12,144,47413035334,20335806334265
  have r13:=row! r12,12,156,3484477592,20339290811857
  have r14:=row! r13,4,160,3496480,20339294308337
  rw [r14]
  decide

private theorem reject5 : zeroMass 22 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=22) (j:=5) (m:=182) (by decide) (Or.inl (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 22 5) 0=0:=rfl
  have r1:=row! r0,12,12,4446500290178,4446500290178
  have r2:=row! r1,12,24,3671041428870,8117541719048
  have r3:=row! r2,12,36,2997291875042,11114833594090
  have r4:=row! r3,12,48,2416232390294,13531065984384
  have r5:=row! r4,12,60,1919252408226,15450318392610
  have r6:=row! r5,12,72,1498150034438,16948468427048
  have r7:=row! r6,12,84,1145132046530,18093600473578
  have r8:=row! r7,12,96,852813894102,18946414367680
  have r9:=row! r8,12,108,614219698754,19560634066434
  have r10:=row! r9,12,120,422782254086,19983416320520
  have r11:=row! r10,12,132,272343025698,20255759346218
  have r12:=row! r11,12,144,157154045616,20412913391834
  have r13:=row! r12,12,156,72455558497,20485368950331
  have r14:=row! r13,12,168,18878847395,20504247797726
  have r15:=row! r14,12,180,1036779119,20505284576845
  have r16:=row! r15,2,182,46871,20505284623716
  rw [r16]
  decide

private theorem reject6 : zeroMass 18 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=18) (j:=6) (m:=222) (by decide) (Or.inl (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 18 6) 0=0:=rfl
  have r1:=row! r0,12,12,4434364264099,4434364264099
  have r2:=row! r1,12,24,3643467092743,8077831356842
  have r3:=row! r2,12,36,2962907954635,11040739311477
  have r4:=row! r3,12,48,2381959640047,13422698951524
  have r5:=row! r4,12,60,1890441374323,15313140325847
  have r6:=row! r5,12,72,1478718817879,16791859143726
  have r7:=row! r6,12,84,1137704066203,17929563209929
  have r8:=row! r7,12,96,858855649855,18788418859784
  have r9:=row! r8,12,108,634178534467,19422597394251
  have r10:=row! r9,12,120,456224120743,19878821514994
  have r11:=row! r10,12,132,318090244459,20196911759453
  have r12:=row! r11,12,144,213421176463,20410332935916
  have r13:=row! r12,12,156,136407622675,20546740558591
  have r14:=row! r13,12,168,81786724087,20628527282678
  have r15:=row! r14,12,180,44842056763,20673369339441
  have r16:=row! r15,12,192,21403631839,20694772971280
  have r17:=row! r16,12,204,7850275839,20702623247119
  have r18:=row! r17,12,216,1352786874,20703976033993
  have r19:=row! r18,6,222,10163916,20703986197909
  rw [r19]
  decide

private theorem reject7 : zeroMass 13 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=13) (j:=7) (m:=235) (by decide) (Or.inr (by decide))]
  have r0:P3_6_8_1.sumBelow (P3_6_8_1.term 13 7) 0=0:=rfl
  have r1:=row! r0,12,12,4430333503446,4430333503446
  have r2:=row! r1,12,24,3633314403210,8063647906656
  have r3:=row! r2,12,36,2948356230022,11012004136678
  have r4:=row! r3,12,48,2364510724938,13376514861616
  have r5:=row! r4,12,60,1871386770774,15247901632390
  have r6:=row! r5,12,72,1459150392106,16707052024496
  have r7:=row! r6,12,84,1118524755270,17825576779766
  have r8:=row! r7,12,96,840790168362,18666366948128
  have r9:=row! r8,12,108,617784081238,19284151029366
  have r10:=row! r9,12,120,441901085514,19726052114880
  have r11:=row! r10,12,132,306092914566,20032145029446
  have r12:=row! r11,12,144,203868443530,20236013472976
  have r13:=row! r12,12,156,129293689302,20365307162278
  have r14:=row! r13,12,168,76991810538,20442298972816
  have r15:=row! r14,12,180,42143107654,20484442080470
  have r16:=row! r15,12,192,20485022826,20504927103296
  have r17:=row! r16,12,204,8312139990,20513239243286
  have r18:=row! r17,12,216,2476184842,20515715428128
  have r19:=row! r18,12,228,386024838,20516101452966
  have r20:=row! r19,7,235,8374990,20516109827956
  rw [r20]
  decide

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers:Final50Price.LayerBudget a l) {z s:Finset (Fin n)} {q:Shape} {L:ℕ}
    (hz : ∀ i ∈ z,l i=0) (hs : ∀ i ∈ s,l i≤L)
    (hdisj:Disjoint z s) (hq:InBox q (P3_6_8.shapeSum a z)) :
    Final50Price.layerNeed ≤ ∑ k ∈ Finset.range layerCount,layerTerm q (P3_6_8.shapeSum a s) L k:=by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => Final50PriceLayer.remaining_anti ?_ ?_)
  · exact P3_6_8.spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact P3_6_8.spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
private theorem zeroMass_upper {b j : ℕ} (hj : 0 < j) :
    (∑ k ∈ Finset.range layerCount, K1_13.remaining ((k + 1) * b) ((k + 1) * j)) ≤
      zeroMass b j:=by
  unfold zeroMass
  simp only [symbol_count]
  rw [K1_13_8.sum_range_min layerCount (1650 / j)
    (fun k hk => K1_13_8.fastRemaining_zero (K1_13_8.index_over hj hk))]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))

private theorem retained_bound {r : Shape} (hr : Valid r) (hindex : r.j ≤ 7)
    (hmass : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      K1_13.remaining ((k+1)*r.b) ((k+1)*r.j)):Box r:=by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall:zeroMass b j < layerNeed):False:=by
    have hle : layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (zeroMass_upper hjpos)
    exact (not_lt_of_ge hle) hsmall
  obtain ⟨ht,hjt,hjb⟩:=hr
  refine ⟨?_,hindex, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject3
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject4
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject5
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject6
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject7

/-- The factors that receive no proper cut have total top degree at most two. -/
theorem no_cut_shape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i,Valid (a i)) (hl:Final50Price.LayerBudget a l)
    (z:Finset (Fin n)) (hz : ∀ i ∈ z,l i=0) (hj:(combined a z).j≤7) :
    z = ∅ ∨ (Box (combined a z) ∧ 1≤(combined a z).t ∧ (combined a z).t≤2):=by
  rcases P3_6_8.shapeSum_valid_or_empty ha z with h | hr
  · exact Or.inl h
  · right
    let r:=P3_6_8.shapeSum a z
    have hb := mass_le hl (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
      (show InBox r r from ⟨le_rfl,le_rfl,le_rfl⟩)
    have hbox : Box r := retained_bound hr hj (by
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
end Final50PriceRetained

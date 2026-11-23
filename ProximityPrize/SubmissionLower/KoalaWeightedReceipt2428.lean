import ProximityPrize.SubmissionLower.KoalaWeightedLayer2428

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 6000000

namespace KoalaWeightedReceipt2428
open K1_13 (Shape InBox)
open K1_13_8 (fastRemaining sum_range_truncate)
open Final50Price (layerNeed symbolCount)
open KoalaWeightedLayer2428 (WeightedLayerBudget layerTerm mass_le)
open H2428Weighted87Count (rawCount boxCount_toNat_le)
open scoped BigOperators
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8
open private P3_6_8.shapeSum from ProximityPrize.SubmissionLower.GoldBranch6N8

private def retained:Shape:=⟨11,7,2⟩
private def left:Shape:=⟨123,48,0⟩
private def right:Shape:=⟨125,49,0⟩

private def rawRemaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then
    min (min symbolCount (fastRemaining b j)) (rawCount (4012-b) (1650-j) (39656-8*b))
  else 0

private theorem remaining_le (b j : ℕ) :
    KoalaWeightedLayer2428.remaining b j≤rawRemaining b j:=by
  unfold KoalaWeightedLayer2428.remaining rawRemaining Final50Price.remaining
  rw [P0_9_8.symbol_count]
  split
  · exact min_le_min le_rfl (boxCount_toNat_le _ _ _)
  · exact le_rfl

private def rawLayer (y : Shape) (L k : ℕ) : ℕ :=
  rawRemaining ((k+1)*11+(k+1-L)*y.b) ((k+1)*7+(k+1-L)*y.j)

private def rawPrefixLayer (k:ℕ):ℕ:=rawRemaining ((k+1)*11) ((k+1)*7)

private theorem prefix_eq (y : Shape) (L : ℕ) (hL : 140 ≤ L) :
    P3_6_8_1.sumBelow (rawLayer y L) 140=P3_6_8_1.sumBelow rawPrefixLayer 140:=by
  rw [P3_6_8_1.sumBelow_eq,P3_6_8_1.sumBelow_eq]
  apply Finset.sum_congr rfl
  intro k hk
  have hh:k+1-L=0:=by have:=Finset.mem_range.mp hk; omega
  simp [rawLayer,rawPrefixLayer,hh]

private theorem join {f : ℕ → ℕ} {a b u v : ℕ}
    (ha:P3_6_8_1.sumBelow f a=u) (hb:P3_6_8_1.sumBelow (fun k => f (a+k)) b=v) :
    P3_6_8_1.sumBelow f (a+b)=u+v:=by rw [P3_6_8_1.sumBelow_add,ha,hb]

private theorem absolute_mass {y : Shape} {L v : ℕ}
    (hL:L≤141) (hj:48≤y.j)
    (hv:P3_6_8_1.sumBelow (rawLayer y L) 170=v) :
    (∑ k ∈ Finset.range Final50PriceLayer.layerCount,layerTerm retained y L k)≤v:=by
  have tails (k : ℕ) (hk : 170 ≤ k) : rawLayer y L k = 0 := by
    have h : 1650 < (k+1)*7+(k+1-L)*y.j := by
      have h0:30≤k+1-L:=by omega
      have h1:=Nat.mul_le_mul h0 hj
      omega
    simp [rawLayer,rawRemaining,not_le_of_gt h]
  calc
    _ ≤ ∑ k ∈ Finset.range Final50PriceLayer.layerCount, rawLayer y L k :=
      Finset.sum_le_sum fun k _ => remaining_le _ _
    _ = ∑ k ∈ Finset.range 170,rawLayer y L k:=sum_range_truncate tails (by decide)
    _=v:=(P3_6_8_1.sumBelow_eq _ _).symm.trans hv

private theorem prefixChunk0:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 8=3045403786250:=by decide +kernel
private theorem prefixChunk8:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (8+k)) 8=2690751587895:=by decide +kernel
private theorem prefixChunk16:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (16+k)) 8=2366930853517:=by decide +kernel
private theorem prefixChunk24:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (24+k)) 8=2072286043026:=by decide +kernel
private theorem prefixChunk32:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (32+k)) 8=1805185581195:=by decide +kernel
private theorem prefixChunk40:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (40+k)) 8=1563875953529:=by decide +kernel
private theorem prefixChunk48:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (48+k)) 8=1346760346380:=by decide +kernel
private theorem prefixChunk56:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (56+k)) 8=1152646879646:=by decide +kernel
private theorem prefixChunk64:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (64+k)) 8=979906692146:=by decide +kernel
private theorem prefixChunk72:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (72+k)) 8=826955046476:=by decide +kernel
private theorem prefixChunk80:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (80+k)) 8=692265590606:=by decide +kernel
private theorem prefixChunk88:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (88+k)) 8=574370352210:=by decide +kernel
private theorem prefixChunk96:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (96+k)) 8=471859741644:=by decide +kernel
private theorem prefixChunk104:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (104+k)) 8=383382554430:=by decide +kernel
private theorem prefixChunk112:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (112+k)) 8=307645966002:=by decide +kernel
private theorem prefixChunk120:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (120+k)) 8=243415534476:=by decide +kernel
private theorem prefixChunk128:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (128+k)) 8=189515202926:=by decide +kernel
private theorem prefixChunk136:P3_6_8_1.sumBelow (fun k => rawPrefixLayer (136+k)) 4=77465922098:=by decide +kernel
private theorem prefixTotal8 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 8 = 3045403786250 := by
  exact prefixChunk0
private theorem prefixTotal16 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 16 = 5736155374145 := by
  have h := join prefixTotal8 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 8+k))) 8 = 2690751587895 from by
    simpa only [← Nat.add_assoc] using prefixChunk8)
  exact h
private theorem prefixTotal24 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 24 = 8103086227662 := by
  have h := join prefixTotal16 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 16+k))) 8 = 2366930853517 from by
    simpa only [← Nat.add_assoc] using prefixChunk16)
  exact h
private theorem prefixTotal32 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 32 = 10175372270688 := by
  have h := join prefixTotal24 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 24+k))) 8 = 2072286043026 from by
    simpa only [← Nat.add_assoc] using prefixChunk24)
  exact h
private theorem prefixTotal40 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 40 = 11980557851883 := by
  have h := join prefixTotal32 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 32+k))) 8 = 1805185581195 from by
    simpa only [← Nat.add_assoc] using prefixChunk32)
  exact h
private theorem prefixTotal48 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 48 = 13544433805412 := by
  have h := join prefixTotal40 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 40+k))) 8 = 1563875953529 from by
    simpa only [← Nat.add_assoc] using prefixChunk40)
  exact h
private theorem prefixTotal56 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 56 = 14891194151792 := by
  have h := join prefixTotal48 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 48+k))) 8 = 1346760346380 from by
    simpa only [← Nat.add_assoc] using prefixChunk48)
  exact h
private theorem prefixTotal64 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 64 = 16043841031438 := by
  have h := join prefixTotal56 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 56+k))) 8 = 1152646879646 from by
    simpa only [← Nat.add_assoc] using prefixChunk56)
  exact h
private theorem prefixTotal72 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 72 = 17023747723584 := by
  have h := join prefixTotal64 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 64+k))) 8 = 979906692146 from by
    simpa only [← Nat.add_assoc] using prefixChunk64)
  exact h
private theorem prefixTotal80 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 80 = 17850702770060 := by
  have h := join prefixTotal72 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 72+k))) 8 = 826955046476 from by
    simpa only [← Nat.add_assoc] using prefixChunk72)
  exact h
private theorem prefixTotal88 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 88 = 18542968360666 := by
  have h := join prefixTotal80 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 80+k))) 8 = 692265590606 from by
    simpa only [← Nat.add_assoc] using prefixChunk80)
  exact h
private theorem prefixTotal96 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 96 = 19117338712876 := by
  have h := join prefixTotal88 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 88+k))) 8 = 574370352210 from by
    simpa only [← Nat.add_assoc] using prefixChunk88)
  exact h
private theorem prefixTotal104 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 104 = 19589198454520 := by
  have h := join prefixTotal96 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 96+k))) 8 = 471859741644 from by
    simpa only [← Nat.add_assoc] using prefixChunk96)
  exact h
private theorem prefixTotal112 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 112 = 19972581008950 := by
  have h := join prefixTotal104 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 104+k))) 8 = 383382554430 from by
    simpa only [← Nat.add_assoc] using prefixChunk104)
  exact h
private theorem prefixTotal120 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 120 = 20280226974952 := by
  have h := join prefixTotal112 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 112+k))) 8 = 307645966002 from by
    simpa only [← Nat.add_assoc] using prefixChunk112)
  exact h
private theorem prefixTotal128 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 128 = 20523642509428 := by
  have h := join prefixTotal120 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 120+k))) 8 = 243415534476 from by
    simpa only [← Nat.add_assoc] using prefixChunk120)
  exact h
private theorem prefixTotal136 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 136 = 20713157712354 := by
  have h := join prefixTotal128 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 128+k))) 8 = 189515202926 from by
    simpa only [← Nat.add_assoc] using prefixChunk128)
  exact h
private theorem prefixTotal140 : P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+k)) 140 = 20790623634452 := by
  have h := join prefixTotal136 (show P3_6_8_1.sumBelow (fun k => rawPrefixLayer (0+( 136+k))) 4 = 77465922098 from by
    simpa only [← Nat.add_assoc] using prefixChunk136)
  exact h
private theorem leftChunk0:P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+k)) 8=40353129585:=by decide +kernel
private theorem leftChunk8:P3_6_8_1.sumBelow (fun k => rawLayer left 140 (148+k)) 8=252544236:=by decide +kernel
private theorem leftChunk16:P3_6_8_1.sumBelow (fun k => rawLayer left 140 (156+k)) 8=0:=by decide +kernel
private theorem leftChunk24:P3_6_8_1.sumBelow (fun k => rawLayer left 140 (164+k)) 6=0:=by decide +kernel
private theorem leftTotal8 : P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+k)) 8 = 40353129585 := by
  exact leftChunk0
private theorem leftTotal16 : P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+k)) 16 = 40605673821 := by
  have h := join leftTotal8 (show P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+( 8+k))) 8 = 252544236 from by
    simpa only [← Nat.add_assoc] using leftChunk8)
  exact h
private theorem leftTotal24 : P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+k)) 24 = 40605673821 := by
  have h := join leftTotal16 (show P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+( 16+k))) 8 = 0 from by
    simpa only [← Nat.add_assoc] using leftChunk16)
  exact h
private theorem leftTotal30 : P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+k)) 30 = 40605673821 := by
  have h := join leftTotal24 (show P3_6_8_1.sumBelow (fun k => rawLayer left 140 (140+( 24+k))) 6 = 0 from by
    simpa only [← Nat.add_assoc] using leftChunk24)
  exact h

theorem left_bound :
    (∑ k ∈ Finset.range Final50PriceLayer.layerCount,layerTerm retained left 140 k)≤20831229308273:=by
  apply absolute_mass (by decide) (by decide)
  exact join ((prefix_eq left 140 (by decide)).trans (by simpa only [Nat.zero_add] using prefixTotal140)) leftTotal30
private theorem rightChunk0:P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+k)) 8=55156252588:=by decide +kernel
private theorem rightChunk8:P3_6_8_1.sumBelow (fun k => rawLayer right 141 (148+k)) 8=547124772:=by decide +kernel
private theorem rightChunk16:P3_6_8_1.sumBelow (fun k => rawLayer right 141 (156+k)) 8=0:=by decide +kernel
private theorem rightChunk24:P3_6_8_1.sumBelow (fun k => rawLayer right 141 (164+k)) 6=0:=by decide +kernel
private theorem rightTotal8 : P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+k)) 8 = 55156252588 := by
  exact rightChunk0
private theorem rightTotal16 : P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+k)) 16 = 55703377360 := by
  have h := join rightTotal8 (show P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+( 8+k))) 8 = 547124772 from by
    simpa only [← Nat.add_assoc] using rightChunk8)
  exact h
private theorem rightTotal24 : P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+k)) 24 = 55703377360 := by
  have h := join rightTotal16 (show P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+( 16+k))) 8 = 0 from by
    simpa only [← Nat.add_assoc] using rightChunk16)
  exact h
private theorem rightTotal30 : P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+k)) 30 = 55703377360 := by
  have h := join rightTotal24 (show P3_6_8_1.sumBelow (fun k => rawLayer right 141 (140+( 24+k))) 6 = 0 from by
    simpa only [← Nat.add_assoc] using rightChunk24)
  exact h

theorem right_bound :
    (∑ k ∈ Finset.range Final50PriceLayer.layerCount,layerTerm retained right 141 k)≤20846327011812:=by
  apply absolute_mass (by decide) (by decide)
  exact join ((prefix_eq right 141 (by decide)).trans (by simpa only [Nat.zero_add] using prefixTotal140)) rightTotal30

def WeightedOrder (r x : Shape) (m : ℕ) : Prop :=
  InBox retained r ∧
    ((m≤141 ∧ 123≤x.b ∧ 48≤x.j) ∨ (m≤142 ∧ 125≤x.b ∧ 49≤x.j))

theorem order {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hneed:20849264424519≤layerNeed)
    (hbudget:WeightedLayerBudget a l) {z:Finset (Fin n)} {i:Fin n} {r:Shape} {m:ℕ}
    (hz : ∀ j ∈ z,l j=0) (hi:i ∉ z)
    (hbox:InBox r (P3_6_8.shapeSum a z))
    (hweight:WeightedOrder r (a i) m):m≤l i:=by
  obtain ⟨hr,hc⟩:=hweight
  have hco : InBox retained (P3_6_8.shapeSum a z) := ⟨hr.1.trans hbox.1,
    hr.2.1.trans hbox.2.1,hr.2.2.trans hbox.2.2⟩
  by_contra! hn
  rcases hc with ⟨hm,hb,hj⟩ | ⟨hm,hb,hj⟩
  · have h := mass_le hbudget hz hi (L := 140) (by omega) hco
      (show InBox left (a i) from ⟨hb,hj,Nat.zero_le _⟩)
    exact (not_lt_of_ge (h.trans left_bound)) ((by decide:20831229308273 < 20849264424519).trans_le hneed)
  · have h := mass_le hbudget hz hi (L := 141) (by omega) hco
      (show InBox right (a i) from ⟨hb,hj,Nat.zero_le _⟩)
    exact (not_lt_of_ge (h.trans right_bound)) ((by decide:20846327011812 < 20849264424519).trans_le hneed)

#print axioms left_bound
#print axioms right_bound
#print axioms order
end KoalaWeightedReceipt2428

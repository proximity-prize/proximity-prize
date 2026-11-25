import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.R6960Low6960Inventory
import ProximityPrize.SubmissionLower.R6960Low6960Fat
import ProximityPrize.SubmissionLower.R6960Low6960FatBanks

-- merged module Final50FatReserve
section Merged_Final50FatReserve
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace Final50FatReserve
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open Final50Price (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)
private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (Final50Price.errors * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (Final50Price.errors * mc + incidenceGap * mq) (32 * incidenceGap * length)
private def isolatedFee : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
private theorem fatPrice_expand (x : Shape) :
    fatPrice x =
      divisorFee x.chamber (fatChart x)
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) (fatChart x))
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) x.chamber) +
      singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) +
      curveFee (mixed32 x.chamber resultantBox resultantBox (fatChart x))
        (mixed32 x.chamber resultantBox resultantBox x.chamber) + isolatedFee := rfl
private theorem chamber_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE x.chamber y.chamber :=
  ⟨max_le_max h.1 h.2.1.le, h.2⟩
private theorem chart_widen (L : ℕ) {x y : Shape} (h : TotalLE x y) :
    TotalLE (chart L x) (chart L y) := by
  refine ⟨?_, by simp only [chart, h.2.1], by simp only [chart, h.2.1, h.2.2]⟩
  dsimp only [chart]
  rw [h.2.1]
  exact max_le_max
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h.1 _)) _) le_rfl
private theorem fatChart_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE (fatChart x) (fatChart y) := by
  have hp := chamber_widen h
  unfold fatChart
  rw [← h.2.2]
  split
  · refine ⟨?_, by simp only [linearChart, hp.2.1], by simp only [linearChart, hp.2.1]⟩
    dsimp only [linearChart]
    rw [hp.2.1]
    exact max_le_max
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hp.1 _)) _) le_rfl
  · exact chart_widen _ hp
private theorem cut_widen {h H : Shape} (hh : TotalLE h H) :
    TotalLE (divisorCut h) (divisorCut H) := by
  refine ⟨?_, by simp only [divisorCut, hh.2.1], by simp only [divisorCut, hh.2.2]⟩
  dsimp only [divisorCut]
  rw [hh.2.1]
  exact max_le_max (max_le_max hh.1 le_rfl) le_rfl
private theorem capped_index (b j t : ℕ) : IndexFits ⟨b, j, min t (j / 3)⟩ := by
  change 3 * min t (j / 3) ≤ j
  exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (by omega)
private theorem fatChart_index (x : Shape) : IndexFits (fatChart x) := by
  unfold fatChart
  split <;> exact capped_index _ _ _
private theorem cut_index {h : Shape} (hh : IndexFits h) : IndexFits (divisorCut h) := by
  change 3 * h.t ≤ h.j at hh
  change 3 * max 1 h.t ≤ max h.j (divisorBox.j + 1)
  rcases le_total 1 h.t with ht | ht
  · rw [max_eq_right ht]
    exact hh.trans (le_max_left _ _)
  · rw [max_eq_left ht]
    exact (show 3 * 1 ≤ divisorBox.j + 1 from by decide).trans (le_max_right _ _)
private theorem ceil_mono {a b l : ℕ} (h : a ≤ b) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)
theorem fatPrice_widen {x y : Shape} (h : TotalLE x y) (hv : IndexFits x) :
    fatPrice x ≤ fatPrice y := by
  have hp := chamber_widen h
  have hh := fatChart_widen h
  have hc := cut_widen hh
  have hp' : IndexFits x.chamber := hv
  have hh' := fatChart_index x
  have hc' := cut_index hh'
  have hbig : IndexFits divisorBox := Nat.zero_le _
  have hq : IndexFits resultantBox := Nat.zero_le _
  rw [fatPrice_expand x, fatPrice_expand y]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) le_rfl
  · have hd := mixed_mono_total hp (TotalLE.refl divisorBox) hc hh hp' hbig hc' hh'
    have hm := mixed_mono_total hp (TotalLE.refl divisorBox) hc hp hp' hbig hc' hp'
    dsimp only [divisorFee]
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_) le_rfl
    · exact ceil_mono (Nat.mul_le_mul_left _ hd)
    · exact ceil_mono hm
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1)
        (by simpa only [pow_two] using Nat.mul_le_mul hh.1 hh.1)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1) hh.1
  · have hs := mixed_mono_total hp hp hh hh hp' hp' hh' hh'
    dsimp only [singularFee]
    rw [← h.2.2]
    split
    · exact Nat.add_le_add (Nat.add_le_add (ceil_mono (Nat.mul_le_mul_left _ hs))
        (Nat.mul_le_mul_left _ (by simpa only [pow_two] using Nat.mul_le_mul h.1 h.1))) le_rfl
    · exact le_rfl
  · have hc := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hh hp' hq hq hh'
    have hm := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hp hp' hq hq hp'
    exact ceil_mono (Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hm))
def degreeCap : ℕ → ℕ
  | 3 => 25
  | 4 => 23
  | 5 => 20
  | 6 => 16
  | 7 => 10
  | _ => 0
def charge (b j t : ℕ) : ℕ :=
  match t, j with
  | 1, 3 =>
    if b ≤ 1 then 2343347415003976
    else 16815154701363143
  | 1, 4 => 30532279541963794
  | 1, 5 => 46409127523914633
  | 1, 6 => 54064306903674190
  | 1, 7 => 48720018058055370
  | 2, 6 =>
    if b ≤ 3 then 78811583990757641
    else if b ≤ 11 then 135278860228783795
    else if b ≤ 13 then 158427079143371143
    else 193964641150607994
  | 2, 7 =>
    if b ≤ 6 then 143089016514969561
    else 194164445885822982
  | _, _ => 0
private theorem price_3_1_1 : fatPrice ⟨1,3,1⟩ ≤ charge 1 3 1 := by
  decide +kernel
private theorem price_3_1_25 : fatPrice ⟨25,3,1⟩ ≤ charge 25 3 1 := by
  decide +kernel
private theorem price_4_1_23 : fatPrice ⟨23,4,1⟩ ≤ charge 23 4 1 := by
  decide +kernel
private theorem price_5_1_20 : fatPrice ⟨20,5,1⟩ ≤ charge 20 5 1 := by
  decide +kernel
private theorem price_6_1_16 : fatPrice ⟨16,6,1⟩ ≤ charge 16 6 1 := by
  decide +kernel
private theorem price_7_1_10 : fatPrice ⟨10,7,1⟩ ≤ charge 10 7 1 := by
  decide +kernel
private theorem price_6_2_3 : fatPrice ⟨3,6,2⟩ ≤ charge 3 6 2 := by
  decide +kernel
private theorem price_6_2_11 : fatPrice ⟨11,6,2⟩ ≤ charge 11 6 2 := by
  decide +kernel
private theorem price_6_2_13 : fatPrice ⟨13,6,2⟩ ≤ charge 13 6 2 := by
  decide +kernel
private theorem price_6_2_16 : fatPrice ⟨16,6,2⟩ ≤ charge 16 6 2 := by
  decide +kernel
private theorem price_7_2_6 : fatPrice ⟨6,7,2⟩ ≤ charge 6 7 2 := by
  decide +kernel
private theorem price_7_2_10 : fatPrice ⟨10,7,2⟩ ≤ charge 10 7 2 := by
  decide +kernel
theorem single (x : Shape) (hv : Valid x) (hj : x.j ≤ 7) (hb : x.b ≤ degreeCap x.j) :
    fatPrice x ≤ charge x.b x.j x.t := by
  obtain ⟨b, j, t⟩ := x
  have hpos : 1 ≤ t := hv.1
  have hindex : 3 * t ≤ j := hv.2.1
  change j ≤ 7 at hj
  have htop : t = 1 ∨ t = 2 := by omega
  rcases htop with rfl | rfl
  · have hcases : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · by_cases hs1 : b ≤ 1
      · simpa [charge, hs1] using
          (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨1,3,1⟩) ⟨hs1, rfl, rfl⟩ hindex).trans price_3_1_1
      · simpa [charge, hs1] using
          (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨25,3,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_3_1_25
    · exact (fatPrice_widen (x := ⟨b,4,1⟩) (y := ⟨23,4,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_4_1_23
    · exact (fatPrice_widen (x := ⟨b,5,1⟩) (y := ⟨20,5,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_5_1_20
    · exact (fatPrice_widen (x := ⟨b,6,1⟩) (y := ⟨16,6,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_6_1_16
    · exact (fatPrice_widen (x := ⟨b,7,1⟩) (y := ⟨10,7,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_7_1_10
  · have hcases : j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl
    · by_cases hs3 : b ≤ 3
      · simpa [charge, hs3] using
          (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨3,6,2⟩) ⟨hs3, rfl, rfl⟩ hindex).trans price_6_2_3
      · by_cases hs11 : b ≤ 11
        · simpa [charge, hs3, hs11] using
            (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨11,6,2⟩) ⟨hs11, rfl, rfl⟩ hindex).trans price_6_2_11
        · by_cases hs13 : b ≤ 13
          · simpa [charge, hs3, hs11, hs13] using
              (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨13,6,2⟩) ⟨hs13, rfl, rfl⟩ hindex).trans price_6_2_13
          · simpa [charge, hs3, hs11, hs13] using
              (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨16,6,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_6_2_16
    · by_cases hs6 : b ≤ 6
      · simpa [charge, hs6] using
          (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨6,7,2⟩) ⟨hs6, rfl, rfl⟩ hindex).trans price_7_2_6
      · simpa [charge, hs6] using
          (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨10,7,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_7_2_10
private def PairCap (j k cap : ℕ) : Prop :=
  (j + k = 6 ∧ (cap = 3 ∨ cap = 11 ∨ cap = 13 ∨ cap = 16)) ∨
  (j + k = 7 ∧ (cap = 6 ∨ cap = 10))
private theorem pair_endpoints (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : PairCap j k cap) :
    ∀ b : Fin (cap+1), j ≤ 3 * b.val → k ≤ 3 * (cap-b.val) →
      fatPrice ⟨b.val,j,1⟩ + fatPrice ⟨cap-b.val,k,1⟩ ≤ charge cap (j + k) 2 := by
  unfold PairCap at hcap
  have indices : (j = 3 ∧ k = 3) ∨ (j = 3 ∧ k = 4) ∨ (j = 4 ∧ k = 3) := by omega
  rcases indices with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have caps : cap = 3 ∨ cap = 11 ∨ cap = 13 ∨ cap = 16 := by omega
    rcases caps with rfl | rfl | rfl | rfl <;> decide +kernel
  · have caps : cap = 6 ∨ cap = 10 := by omega
    rcases caps with rfl | rfl <;> decide +kernel
  · have caps : cap = 6 ∨ cap = 10 := by omega
    rcases caps with rfl | rfl <;> decide +kernel
private theorem pair_width (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : PairCap j k cap)
    (b c : ℕ) (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ cap) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge cap (j + k) 2 := by
  have hc' : c ≤ cap-b := by omega
  have hck : k ≤ 3 * (cap-b) := hc.trans (Nat.mul_le_mul_left 3 hc')
  have hfee := fatPrice_widen (x := ⟨c,k,1⟩) (y := ⟨cap-b,k,1⟩) ⟨hc', rfl, rfl⟩ hjk.2.1
  exact (Nat.add_le_add_left hfee _).trans
    (pair_endpoints j k cap hjk hcap ⟨b, by omega⟩ hb hck)
theorem pair (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) (hjk : j + k ≤ 7)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge (b+c) (j+k) 2 := by
  have indices : j + k = 6 ∨ j + k = 7 := by omega
  rcases indices with h | h
  · by_cases hs3 : b + c ≤ 3
    · have paid := pair_width j k 3 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs3
      simpa [charge, hs3, h] using paid
    · by_cases hs11 : b + c ≤ 11
      · have paid := pair_width j k 11 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs11
        simpa [charge, hs3, hs11, h] using paid
      · by_cases hs13 : b + c ≤ 13
        · have paid := pair_width j k 13 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs13
          simpa [charge, hs3, hs11, hs13, h] using paid
        · have paid := pair_width j k 16 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc (by simpa only [h, degreeCap] using hbc)
          simpa [charge, hs3, hs11, hs13, h] using paid
  · by_cases hs6 : b + c ≤ 6
    · have paid := pair_width j k 6 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs6
      simpa [charge, hs6, h] using paid
    · have paid := pair_width j k 10 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc (by simpa only [h, degreeCap] using hbc)
      simpa [charge, hs6, h] using paid
theorem family (n : ℕ) (a : Fin n → Shape) (hv : ∀ i, Valid (a i))
    (hj : (∑ i, (a i).j) ≤ 7)
    (hb : (∑ i, (a i).b) ≤ degreeCap (∑ i, (a i).j)) :
    (∑ i, fatPrice (a i)) ≤ charge (∑ i, (a i).b) (∑ i, (a i).j) (∑ i, (a i).t) := by
  have hsum : 3 * (∑ i, (a i).t) ≤ ∑ i, (a i).j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2.1
  have hn' : n ≤ ∑ i, (a i).t := calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i, (a i).t := Finset.sum_le_sum fun i _ => (hv i).1
  have hn : n ≤ 2 := by omega
  interval_cases n
  · simp [charge]
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    exact single _ (hv 0) hj hb
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 := (hv 0).1
    have ht1 := (hv 1).1
    have h0 : (a 0).t = 1 := by omega
    have h1 : (a 1).t = 1 := by omega
    have he (i : Fin 2) : a i = ⟨(a i).b, (a i).j, (a i).t⟩ := by cases a i; rfl
    have hh := pair (a 0).b (a 1).b (a 0).j (a 1).j
      (by simpa only [h0] using (hv 0).2.1) (by simpa only [h1] using (hv 1).2.1)
      hj (hv 0).2.2 (hv 1).2.2 hb
    have ha0 : a 0 = ⟨(a 0).b, (a 0).j, 1⟩ :=
      (he 0).trans (congrArg (fun t => (⟨(a 0).b, (a 0).j, t⟩ : Shape)) h0)
    have ha1 : a 1 = ⟨(a 1).b, (a 1).j, 1⟩ :=
      (he 1).trans (congrArg (fun t => (⟨(a 1).b, (a 1).j, t⟩ : Shape)) h1)
    rw [h0, h1]
    simpa only [← ha0, ← ha1] using hh
#print axioms fatPrice_widen
#print axioms single
#print axioms pair
#print axioms family
end Final50FatReserve

end Merged_Final50FatReserve

-- merged module R6960Low6960RetainedFees
section Merged_R6960Low6960RetainedFees
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Lower6960.Low
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)
open Low6960Fat (commonBox resultantBox)
open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical
abbrev errors : ℕ := 262144-agreement
abbrev incidenceGap : ℕ := agreement-physicalDegree
abbrev taylorLength : ℕ := physicalDegree+1
abbrev fatOrder : ℕ := 23389
abbrev divisorOrder : ℕ := 21672
abbrev isolatedOrder : ℕ := 173
def lowDegreeCap : ℕ → ℕ
  | 3 => 26
  | 4 => 24
  | 5 => 21
  | 6 => 17
  | 7 => 12
  | 8 => 4
  | _ => 0
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
def retainedTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 2016111233507680, 2016111233507680, 2016111233507680, 2334118990588647, 2659424796323294, 2994164662218300, 3340474599780347, 3700490620516113, 4076348735932280, 4470184957535526, 4884135296832534, 5320335765329980, 5780922374534547, 6268031135952914, 6783798061091760, 7330359161457766, 7909850448557613, 8524407933897980, 9176167628985547, 9867265545326993, 10599837694429000, 11376020087798246, 12197948736941413, 13067759653365179, 13987588848576227, 14959572334081233]
  | 4,1 => [0, 0, 4716982938767152, 4716982938767152, 4716982938767152, 5506972063888026, 6306395249169259, 7117388506117532, 7942087846239525, 8782629281041919, 9641148822031391, 10519782480714625, 11420666268598298, 12345936197189091, 13297728277993684, 14278178522518758, 15289422942270990, 16333597548757065, 17412838353483657, 18529281367957450, 19685062603685124, 20882318072173357, 22123183784928829, 23409795753458223, 24744289989268216]
  | 5,1 => [0, 0, 10028614136755384, 10028614136755384, 10028614136755384, 10028614136755384, 11499363082846400, 12981682100604454, 14477707201536229, 15989574397148403, 17519419698947658, 19069379118440672, 20641588667134127, 22238184356534701, 23861302198149076, 25513078203483929, 27195648384045944, 28911148751341798, 30661715316878173, 32449484092161747, 34276591088699202, 36145172317997216]
  | 6,1 => [0, 0, 17382647103884709, 17382647103884709, 17382647103884709, 17382647103884709, 17382647103884709, 19484890076782283, 21600839132853576, 23732630283605271, 25882399540544044, 28052282915176578, 30244416419009551, 32460936063549645, 34703977860303538, 36975677820777913, 39278171956479446, 41613596278914820]
  | 7,1 => [0, 0, 0, 26902156543304570, 26902156543304570, 26902156543304570, 26902156543304570, 26902156543304570, 29638029554515382, 32389744660406595, 35159437872484888, 37949245202256941, 40761302661229433]
  | 8,1 => [0, 0, 0, 38589278466521646, 38589278466521646]
  | 6,2 => [0, 0, 56613603477221896, 56613603477221906, 56613603477221920, 56613603477221938, 56613603477221960, 64595094064728125, 72631056219757014, 80730034500664307, 88900573465805685, 97151217673536826, 105490511682213412, 113927000050191121, 122469227335825635, 131125738097472632, 139905076893487793, 148815788282226799]
  | 7,2 => [0, 0, 0, 102243998670475429, 102243998670475443, 102243998670475461, 102243998670475483, 102243998670475509, 114340069644710352, 126499156744823599, 138729804529170930, 151040557556108025, 163439960383990564]
  | 8,2 => [0, 0, 0, 162789925648465449, 162789925648465463]
  | _,_ => []
def retainedTariff (b j t : ℕ) : ℕ := (retainedTariffs j t).getD b 0
def singleTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 2016111233507680, 2016111233507680, 2016111233507680, 2334118990588647, 2659424796323294, 2994164662218300, 3340474599780347, 3700490620516113, 4076348735932280, 4470184957535526, 4884135296832534, 5320335765329980, 5780922374534547, 6268031135952914, 6783798061091760, 7330359161457766, 7909850448557613, 8524407933897980, 9176167628985547, 9867265545326993, 10599837694429000, 11376020087798246, 12197948736941413, 13067759653365179, 13987588848576227, 14959572334081233]
  | 4,1 => [0, 0, 4716982938767152, 4716982938767152, 4716982938767152, 5506972063888026, 6306395249169259, 7117388506117532, 7942087846239525, 8782629281041919, 9641148822031391, 10519782480714625, 11420666268598298, 12345936197189091, 13297728277993684, 14278178522518758, 15289422942270990, 16333597548757065, 17412838353483657, 18529281367957450, 19685062603685124, 20882318072173357, 22123183784928829, 23409795753458223, 24744289989268216]
  | 5,1 => [0, 0, 10028614136755384, 10028614136755384, 10028614136755384, 10028614136755384, 11499363082846400, 12981682100604454, 14477707201536229, 15989574397148403, 17519419698947658, 19069379118440672, 20641588667134127, 22238184356534701, 23861302198149076, 25513078203483929, 27195648384045944, 28911148751341798, 30661715316878173, 32449484092161747, 34276591088699202, 36145172317997216]
  | 6,1 => [0, 0, 17382647103884709, 17382647103884709, 17382647103884709, 17382647103884709, 17382647103884709, 19484890076782283, 21600839132853576, 23732630283605271, 25882399540544044, 28052282915176578, 30244416419009551, 32460936063549645, 34703977860303538, 36975677820777913, 39278171956479446, 41613596278914820]
  | 7,1 => [0, 0, 0, 26902156543304570, 26902156543304570, 26902156543304570, 26902156543304570, 26902156543304570, 29638029554515382, 32389744660406595, 35159437872484888, 37949245202256941, 40761302661229433]
  | 8,1 => [0, 0, 0, 38589278466521646, 38589278466521646]
  | 6,2 => [0, 0, 56613603477221896, 56613603477221906, 56613603477221920, 56613603477221938, 56613603477221960, 64595094064728125, 72631056219757014, 80730034500664307, 88900573465805685, 97151217673536826, 105490511682213412, 113927000050191121, 122469227335825635, 131125738097472632, 139905076893487793, 148815788282226799]
  | 7,2 => [0, 0, 0, 102243998670475429, 102243998670475443, 102243998670475461, 102243998670475483, 102243998670475509, 114340069644710352, 126499156744823599, 138729804529170930, 151040557556108025, 163439960383990564]
  | 8,2 => [0, 0, 0, 162789925648465449, 162789925648465463]
  | _,_ => []
def singleTariff (b j t : ℕ) : ℕ := (singleTariffs j t).getD b 0
private theorem cell_1_3_1 : fatPrice ⟨1,3,1⟩ ≤ singleTariff 1 3 1 := by decide +kernel
private theorem cell_2_3_1 : fatPrice ⟨2,3,1⟩ ≤ singleTariff 2 3 1 := by decide +kernel
private theorem cell_3_3_1 : fatPrice ⟨3,3,1⟩ ≤ singleTariff 3 3 1 := by decide +kernel
private theorem cell_4_3_1 : fatPrice ⟨4,3,1⟩ ≤ singleTariff 4 3 1 := by decide +kernel
private theorem cell_5_3_1 : fatPrice ⟨5,3,1⟩ ≤ singleTariff 5 3 1 := by decide +kernel
private theorem cell_6_3_1 : fatPrice ⟨6,3,1⟩ ≤ singleTariff 6 3 1 := by decide +kernel
private theorem cell_7_3_1 : fatPrice ⟨7,3,1⟩ ≤ singleTariff 7 3 1 := by decide +kernel
private theorem cell_8_3_1 : fatPrice ⟨8,3,1⟩ ≤ singleTariff 8 3 1 := by decide +kernel
private theorem cell_9_3_1 : fatPrice ⟨9,3,1⟩ ≤ singleTariff 9 3 1 := by decide +kernel
private theorem cell_10_3_1 : fatPrice ⟨10,3,1⟩ ≤ singleTariff 10 3 1 := by decide +kernel
private theorem cell_11_3_1 : fatPrice ⟨11,3,1⟩ ≤ singleTariff 11 3 1 := by decide +kernel
private theorem cell_12_3_1 : fatPrice ⟨12,3,1⟩ ≤ singleTariff 12 3 1 := by decide +kernel
private theorem cell_13_3_1 : fatPrice ⟨13,3,1⟩ ≤ singleTariff 13 3 1 := by decide +kernel
private theorem cell_14_3_1 : fatPrice ⟨14,3,1⟩ ≤ singleTariff 14 3 1 := by decide +kernel
private theorem cell_15_3_1 : fatPrice ⟨15,3,1⟩ ≤ singleTariff 15 3 1 := by decide +kernel
private theorem cell_16_3_1 : fatPrice ⟨16,3,1⟩ ≤ singleTariff 16 3 1 := by decide +kernel
private theorem cell_17_3_1 : fatPrice ⟨17,3,1⟩ ≤ singleTariff 17 3 1 := by decide +kernel
private theorem cell_18_3_1 : fatPrice ⟨18,3,1⟩ ≤ singleTariff 18 3 1 := by decide +kernel
private theorem cell_19_3_1 : fatPrice ⟨19,3,1⟩ ≤ singleTariff 19 3 1 := by decide +kernel
private theorem cell_20_3_1 : fatPrice ⟨20,3,1⟩ ≤ singleTariff 20 3 1 := by decide +kernel
private theorem cell_21_3_1 : fatPrice ⟨21,3,1⟩ ≤ singleTariff 21 3 1 := by decide +kernel
private theorem cell_22_3_1 : fatPrice ⟨22,3,1⟩ ≤ singleTariff 22 3 1 := by decide +kernel
private theorem cell_23_3_1 : fatPrice ⟨23,3,1⟩ ≤ singleTariff 23 3 1 := by decide +kernel
private theorem cell_24_3_1 : fatPrice ⟨24,3,1⟩ ≤ singleTariff 24 3 1 := by decide +kernel
private theorem cell_25_3_1 : fatPrice ⟨25,3,1⟩ ≤ singleTariff 25 3 1 := by decide +kernel
private theorem cell_26_3_1 : fatPrice ⟨26,3,1⟩ ≤ singleTariff 26 3 1 := by decide +kernel
private theorem cell_2_4_1 : fatPrice ⟨2,4,1⟩ ≤ singleTariff 2 4 1 := by decide +kernel
private theorem cell_3_4_1 : fatPrice ⟨3,4,1⟩ ≤ singleTariff 3 4 1 := by decide +kernel
private theorem cell_4_4_1 : fatPrice ⟨4,4,1⟩ ≤ singleTariff 4 4 1 := by decide +kernel
private theorem cell_5_4_1 : fatPrice ⟨5,4,1⟩ ≤ singleTariff 5 4 1 := by decide +kernel
private theorem cell_6_4_1 : fatPrice ⟨6,4,1⟩ ≤ singleTariff 6 4 1 := by decide +kernel
private theorem cell_7_4_1 : fatPrice ⟨7,4,1⟩ ≤ singleTariff 7 4 1 := by decide +kernel
private theorem cell_8_4_1 : fatPrice ⟨8,4,1⟩ ≤ singleTariff 8 4 1 := by decide +kernel
private theorem cell_9_4_1 : fatPrice ⟨9,4,1⟩ ≤ singleTariff 9 4 1 := by decide +kernel
private theorem cell_10_4_1 : fatPrice ⟨10,4,1⟩ ≤ singleTariff 10 4 1 := by decide +kernel
private theorem cell_11_4_1 : fatPrice ⟨11,4,1⟩ ≤ singleTariff 11 4 1 := by decide +kernel
private theorem cell_12_4_1 : fatPrice ⟨12,4,1⟩ ≤ singleTariff 12 4 1 := by decide +kernel
private theorem cell_13_4_1 : fatPrice ⟨13,4,1⟩ ≤ singleTariff 13 4 1 := by decide +kernel
private theorem cell_14_4_1 : fatPrice ⟨14,4,1⟩ ≤ singleTariff 14 4 1 := by decide +kernel
private theorem cell_15_4_1 : fatPrice ⟨15,4,1⟩ ≤ singleTariff 15 4 1 := by decide +kernel
private theorem cell_16_4_1 : fatPrice ⟨16,4,1⟩ ≤ singleTariff 16 4 1 := by decide +kernel
private theorem cell_17_4_1 : fatPrice ⟨17,4,1⟩ ≤ singleTariff 17 4 1 := by decide +kernel
private theorem cell_18_4_1 : fatPrice ⟨18,4,1⟩ ≤ singleTariff 18 4 1 := by decide +kernel
private theorem cell_19_4_1 : fatPrice ⟨19,4,1⟩ ≤ singleTariff 19 4 1 := by decide +kernel
private theorem cell_20_4_1 : fatPrice ⟨20,4,1⟩ ≤ singleTariff 20 4 1 := by decide +kernel
private theorem cell_21_4_1 : fatPrice ⟨21,4,1⟩ ≤ singleTariff 21 4 1 := by decide +kernel
private theorem cell_22_4_1 : fatPrice ⟨22,4,1⟩ ≤ singleTariff 22 4 1 := by decide +kernel
private theorem cell_23_4_1 : fatPrice ⟨23,4,1⟩ ≤ singleTariff 23 4 1 := by decide +kernel
private theorem cell_24_4_1 : fatPrice ⟨24,4,1⟩ ≤ singleTariff 24 4 1 := by decide +kernel
private theorem cell_2_5_1 : fatPrice ⟨2,5,1⟩ ≤ singleTariff 2 5 1 := by decide +kernel
private theorem cell_3_5_1 : fatPrice ⟨3,5,1⟩ ≤ singleTariff 3 5 1 := by decide +kernel
private theorem cell_4_5_1 : fatPrice ⟨4,5,1⟩ ≤ singleTariff 4 5 1 := by decide +kernel
private theorem cell_5_5_1 : fatPrice ⟨5,5,1⟩ ≤ singleTariff 5 5 1 := by decide +kernel
private theorem cell_6_5_1 : fatPrice ⟨6,5,1⟩ ≤ singleTariff 6 5 1 := by decide +kernel
private theorem cell_7_5_1 : fatPrice ⟨7,5,1⟩ ≤ singleTariff 7 5 1 := by decide +kernel
private theorem cell_8_5_1 : fatPrice ⟨8,5,1⟩ ≤ singleTariff 8 5 1 := by decide +kernel
private theorem cell_9_5_1 : fatPrice ⟨9,5,1⟩ ≤ singleTariff 9 5 1 := by decide +kernel
private theorem cell_10_5_1 : fatPrice ⟨10,5,1⟩ ≤ singleTariff 10 5 1 := by decide +kernel
private theorem cell_11_5_1 : fatPrice ⟨11,5,1⟩ ≤ singleTariff 11 5 1 := by decide +kernel
private theorem cell_12_5_1 : fatPrice ⟨12,5,1⟩ ≤ singleTariff 12 5 1 := by decide +kernel
private theorem cell_13_5_1 : fatPrice ⟨13,5,1⟩ ≤ singleTariff 13 5 1 := by decide +kernel
private theorem cell_14_5_1 : fatPrice ⟨14,5,1⟩ ≤ singleTariff 14 5 1 := by decide +kernel
private theorem cell_15_5_1 : fatPrice ⟨15,5,1⟩ ≤ singleTariff 15 5 1 := by decide +kernel
private theorem cell_16_5_1 : fatPrice ⟨16,5,1⟩ ≤ singleTariff 16 5 1 := by decide +kernel
private theorem cell_17_5_1 : fatPrice ⟨17,5,1⟩ ≤ singleTariff 17 5 1 := by decide +kernel
private theorem cell_18_5_1 : fatPrice ⟨18,5,1⟩ ≤ singleTariff 18 5 1 := by decide +kernel
private theorem cell_19_5_1 : fatPrice ⟨19,5,1⟩ ≤ singleTariff 19 5 1 := by decide +kernel
private theorem cell_20_5_1 : fatPrice ⟨20,5,1⟩ ≤ singleTariff 20 5 1 := by decide +kernel
private theorem cell_21_5_1 : fatPrice ⟨21,5,1⟩ ≤ singleTariff 21 5 1 := by decide +kernel
private theorem cell_2_6_1 : fatPrice ⟨2,6,1⟩ ≤ singleTariff 2 6 1 := by decide +kernel
private theorem cell_3_6_1 : fatPrice ⟨3,6,1⟩ ≤ singleTariff 3 6 1 := by decide +kernel
private theorem cell_4_6_1 : fatPrice ⟨4,6,1⟩ ≤ singleTariff 4 6 1 := by decide +kernel
private theorem cell_5_6_1 : fatPrice ⟨5,6,1⟩ ≤ singleTariff 5 6 1 := by decide +kernel
private theorem cell_6_6_1 : fatPrice ⟨6,6,1⟩ ≤ singleTariff 6 6 1 := by decide +kernel
private theorem cell_7_6_1 : fatPrice ⟨7,6,1⟩ ≤ singleTariff 7 6 1 := by decide +kernel
private theorem cell_8_6_1 : fatPrice ⟨8,6,1⟩ ≤ singleTariff 8 6 1 := by decide +kernel
private theorem cell_9_6_1 : fatPrice ⟨9,6,1⟩ ≤ singleTariff 9 6 1 := by decide +kernel
private theorem cell_10_6_1 : fatPrice ⟨10,6,1⟩ ≤ singleTariff 10 6 1 := by decide +kernel
private theorem cell_11_6_1 : fatPrice ⟨11,6,1⟩ ≤ singleTariff 11 6 1 := by decide +kernel
private theorem cell_12_6_1 : fatPrice ⟨12,6,1⟩ ≤ singleTariff 12 6 1 := by decide +kernel
private theorem cell_13_6_1 : fatPrice ⟨13,6,1⟩ ≤ singleTariff 13 6 1 := by decide +kernel
private theorem cell_14_6_1 : fatPrice ⟨14,6,1⟩ ≤ singleTariff 14 6 1 := by decide +kernel
private theorem cell_15_6_1 : fatPrice ⟨15,6,1⟩ ≤ singleTariff 15 6 1 := by decide +kernel
private theorem cell_16_6_1 : fatPrice ⟨16,6,1⟩ ≤ singleTariff 16 6 1 := by decide +kernel
private theorem cell_17_6_1 : fatPrice ⟨17,6,1⟩ ≤ singleTariff 17 6 1 := by decide +kernel
private theorem cell_3_7_1 : fatPrice ⟨3,7,1⟩ ≤ singleTariff 3 7 1 := by decide +kernel
private theorem cell_4_7_1 : fatPrice ⟨4,7,1⟩ ≤ singleTariff 4 7 1 := by decide +kernel
private theorem cell_5_7_1 : fatPrice ⟨5,7,1⟩ ≤ singleTariff 5 7 1 := by decide +kernel
private theorem cell_6_7_1 : fatPrice ⟨6,7,1⟩ ≤ singleTariff 6 7 1 := by decide +kernel
private theorem cell_7_7_1 : fatPrice ⟨7,7,1⟩ ≤ singleTariff 7 7 1 := by decide +kernel
private theorem cell_8_7_1 : fatPrice ⟨8,7,1⟩ ≤ singleTariff 8 7 1 := by decide +kernel
private theorem cell_9_7_1 : fatPrice ⟨9,7,1⟩ ≤ singleTariff 9 7 1 := by decide +kernel
private theorem cell_10_7_1 : fatPrice ⟨10,7,1⟩ ≤ singleTariff 10 7 1 := by decide +kernel
private theorem cell_11_7_1 : fatPrice ⟨11,7,1⟩ ≤ singleTariff 11 7 1 := by decide +kernel
private theorem cell_12_7_1 : fatPrice ⟨12,7,1⟩ ≤ singleTariff 12 7 1 := by decide +kernel
private theorem cell_3_8_1 : fatPrice ⟨3,8,1⟩ ≤ singleTariff 3 8 1 := by decide +kernel
private theorem cell_4_8_1 : fatPrice ⟨4,8,1⟩ ≤ singleTariff 4 8 1 := by decide +kernel
private theorem cell_2_6_2 : fatPrice ⟨2,6,2⟩ ≤ singleTariff 2 6 2 := by decide +kernel
private theorem cell_3_6_2 : fatPrice ⟨3,6,2⟩ ≤ singleTariff 3 6 2 := by decide +kernel
private theorem cell_4_6_2 : fatPrice ⟨4,6,2⟩ ≤ singleTariff 4 6 2 := by decide +kernel
private theorem cell_5_6_2 : fatPrice ⟨5,6,2⟩ ≤ singleTariff 5 6 2 := by decide +kernel
private theorem cell_6_6_2 : fatPrice ⟨6,6,2⟩ ≤ singleTariff 6 6 2 := by decide +kernel
private theorem cell_7_6_2 : fatPrice ⟨7,6,2⟩ ≤ singleTariff 7 6 2 := by decide +kernel
private theorem cell_8_6_2 : fatPrice ⟨8,6,2⟩ ≤ singleTariff 8 6 2 := by decide +kernel
private theorem cell_9_6_2 : fatPrice ⟨9,6,2⟩ ≤ singleTariff 9 6 2 := by decide +kernel
private theorem cell_10_6_2 : fatPrice ⟨10,6,2⟩ ≤ singleTariff 10 6 2 := by decide +kernel
private theorem cell_11_6_2 : fatPrice ⟨11,6,2⟩ ≤ singleTariff 11 6 2 := by decide +kernel
private theorem cell_12_6_2 : fatPrice ⟨12,6,2⟩ ≤ singleTariff 12 6 2 := by decide +kernel
private theorem cell_13_6_2 : fatPrice ⟨13,6,2⟩ ≤ singleTariff 13 6 2 := by decide +kernel
private theorem cell_14_6_2 : fatPrice ⟨14,6,2⟩ ≤ singleTariff 14 6 2 := by decide +kernel
private theorem cell_15_6_2 : fatPrice ⟨15,6,2⟩ ≤ singleTariff 15 6 2 := by decide +kernel
private theorem cell_16_6_2 : fatPrice ⟨16,6,2⟩ ≤ singleTariff 16 6 2 := by decide +kernel
private theorem cell_17_6_2 : fatPrice ⟨17,6,2⟩ ≤ singleTariff 17 6 2 := by decide +kernel
private theorem cell_3_7_2 : fatPrice ⟨3,7,2⟩ ≤ singleTariff 3 7 2 := by decide +kernel
private theorem cell_4_7_2 : fatPrice ⟨4,7,2⟩ ≤ singleTariff 4 7 2 := by decide +kernel
private theorem cell_5_7_2 : fatPrice ⟨5,7,2⟩ ≤ singleTariff 5 7 2 := by decide +kernel
private theorem cell_6_7_2 : fatPrice ⟨6,7,2⟩ ≤ singleTariff 6 7 2 := by decide +kernel
private theorem cell_7_7_2 : fatPrice ⟨7,7,2⟩ ≤ singleTariff 7 7 2 := by decide +kernel
private theorem cell_8_7_2 : fatPrice ⟨8,7,2⟩ ≤ singleTariff 8 7 2 := by decide +kernel
private theorem cell_9_7_2 : fatPrice ⟨9,7,2⟩ ≤ singleTariff 9 7 2 := by decide +kernel
private theorem cell_10_7_2 : fatPrice ⟨10,7,2⟩ ≤ singleTariff 10 7 2 := by decide +kernel
private theorem cell_11_7_2 : fatPrice ⟨11,7,2⟩ ≤ singleTariff 11 7 2 := by decide +kernel
private theorem cell_12_7_2 : fatPrice ⟨12,7,2⟩ ≤ singleTariff 12 7 2 := by decide +kernel
private theorem cell_3_8_2 : fatPrice ⟨3,8,2⟩ ≤ singleTariff 3 8 2 := by decide +kernel
private theorem cell_4_8_2 : fatPrice ⟨4,8,2⟩ ≤ singleTariff 4 8 2 := by decide +kernel
private theorem price_3_1 (b : ℕ) (lo : 1≤b) (hi : b≤26) :
    fatPrice ⟨b,3,1⟩ ≤ singleTariff b 3 1 := by
  interval_cases b
  · exact cell_1_3_1
  · exact cell_2_3_1
  · exact cell_3_3_1
  · exact cell_4_3_1
  · exact cell_5_3_1
  · exact cell_6_3_1
  · exact cell_7_3_1
  · exact cell_8_3_1
  · exact cell_9_3_1
  · exact cell_10_3_1
  · exact cell_11_3_1
  · exact cell_12_3_1
  · exact cell_13_3_1
  · exact cell_14_3_1
  · exact cell_15_3_1
  · exact cell_16_3_1
  · exact cell_17_3_1
  · exact cell_18_3_1
  · exact cell_19_3_1
  · exact cell_20_3_1
  · exact cell_21_3_1
  · exact cell_22_3_1
  · exact cell_23_3_1
  · exact cell_24_3_1
  · exact cell_25_3_1
  · exact cell_26_3_1
private theorem price_4_1 (b : ℕ) (lo : 2≤b) (hi : b≤24) :
    fatPrice ⟨b,4,1⟩ ≤ singleTariff b 4 1 := by
  interval_cases b
  · exact cell_2_4_1
  · exact cell_3_4_1
  · exact cell_4_4_1
  · exact cell_5_4_1
  · exact cell_6_4_1
  · exact cell_7_4_1
  · exact cell_8_4_1
  · exact cell_9_4_1
  · exact cell_10_4_1
  · exact cell_11_4_1
  · exact cell_12_4_1
  · exact cell_13_4_1
  · exact cell_14_4_1
  · exact cell_15_4_1
  · exact cell_16_4_1
  · exact cell_17_4_1
  · exact cell_18_4_1
  · exact cell_19_4_1
  · exact cell_20_4_1
  · exact cell_21_4_1
  · exact cell_22_4_1
  · exact cell_23_4_1
  · exact cell_24_4_1
private theorem price_5_1 (b : ℕ) (lo : 2≤b) (hi : b≤21) :
    fatPrice ⟨b,5,1⟩ ≤ singleTariff b 5 1 := by
  interval_cases b
  · exact cell_2_5_1
  · exact cell_3_5_1
  · exact cell_4_5_1
  · exact cell_5_5_1
  · exact cell_6_5_1
  · exact cell_7_5_1
  · exact cell_8_5_1
  · exact cell_9_5_1
  · exact cell_10_5_1
  · exact cell_11_5_1
  · exact cell_12_5_1
  · exact cell_13_5_1
  · exact cell_14_5_1
  · exact cell_15_5_1
  · exact cell_16_5_1
  · exact cell_17_5_1
  · exact cell_18_5_1
  · exact cell_19_5_1
  · exact cell_20_5_1
  · exact cell_21_5_1
private theorem price_6_1 (b : ℕ) (lo : 2≤b) (hi : b≤17) :
    fatPrice ⟨b,6,1⟩ ≤ singleTariff b 6 1 := by
  interval_cases b
  · exact cell_2_6_1
  · exact cell_3_6_1
  · exact cell_4_6_1
  · exact cell_5_6_1
  · exact cell_6_6_1
  · exact cell_7_6_1
  · exact cell_8_6_1
  · exact cell_9_6_1
  · exact cell_10_6_1
  · exact cell_11_6_1
  · exact cell_12_6_1
  · exact cell_13_6_1
  · exact cell_14_6_1
  · exact cell_15_6_1
  · exact cell_16_6_1
  · exact cell_17_6_1
private theorem price_7_1 (b : ℕ) (lo : 3≤b) (hi : b≤12) :
    fatPrice ⟨b,7,1⟩ ≤ singleTariff b 7 1 := by
  interval_cases b
  · exact cell_3_7_1
  · exact cell_4_7_1
  · exact cell_5_7_1
  · exact cell_6_7_1
  · exact cell_7_7_1
  · exact cell_8_7_1
  · exact cell_9_7_1
  · exact cell_10_7_1
  · exact cell_11_7_1
  · exact cell_12_7_1
private theorem price_8_1 (b : ℕ) (lo : 3≤b) (hi : b≤4) :
    fatPrice ⟨b,8,1⟩ ≤ singleTariff b 8 1 := by
  interval_cases b
  · exact cell_3_8_1
  · exact cell_4_8_1
private theorem price_6_2 (b : ℕ) (lo : 2≤b) (hi : b≤17) :
    fatPrice ⟨b,6,2⟩ ≤ singleTariff b 6 2 := by
  interval_cases b
  · exact cell_2_6_2
  · exact cell_3_6_2
  · exact cell_4_6_2
  · exact cell_5_6_2
  · exact cell_6_6_2
  · exact cell_7_6_2
  · exact cell_8_6_2
  · exact cell_9_6_2
  · exact cell_10_6_2
  · exact cell_11_6_2
  · exact cell_12_6_2
  · exact cell_13_6_2
  · exact cell_14_6_2
  · exact cell_15_6_2
  · exact cell_16_6_2
  · exact cell_17_6_2
private theorem price_7_2 (b : ℕ) (lo : 3≤b) (hi : b≤12) :
    fatPrice ⟨b,7,2⟩ ≤ singleTariff b 7 2 := by
  interval_cases b
  · exact cell_3_7_2
  · exact cell_4_7_2
  · exact cell_5_7_2
  · exact cell_6_7_2
  · exact cell_7_7_2
  · exact cell_8_7_2
  · exact cell_9_7_2
  · exact cell_10_7_2
  · exact cell_11_7_2
  · exact cell_12_7_2
private theorem price_8_2 (b : ℕ) (lo : 3≤b) (hi : b≤4) :
    fatPrice ⟨b,8,2⟩ ≤ singleTariff b 8 2 := by
  interval_cases b
  · exact cell_3_8_2
  · exact cell_4_8_2
private theorem single_price {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    fatPrice ⟨b,j,t⟩≤singleTariff b j t := by
  have ht2 : t≤2 := by omega
  interval_cases t
  · have jl : 3≤j := by omega
    interval_cases j
    · exact price_3_1 b (by omega) hb
    · exact price_4_1 b (by omega) hb
    · exact price_5_1 b (by omega) hb
    · exact price_6_1 b (by omega) hb
    · exact price_7_1 b (by omega) hb
    · exact price_8_1 b (by omega) hb
  · have jl : 6≤j := by omega
    interval_cases j
    · exact price_6_2 b (by omega) hb
    · exact price_7_2 b (by omega) hb
    · exact price_8_2 b (by omega) hb
private def splitPrices (b j : ℕ) : List ℕ :=
  (List.range (b+1)).flatMap (fun c=>(List.range (j+1)).map (fun k=>
    if 3≤k ∧ k≤3*c ∧ 3≤j-k ∧ j-k≤3*(b-c) then
      singleTariff c k 1+singleTariff (b-c) (j-k) 1 else 0))
private def widthCharge (b j t : ℕ) : ℕ :=
  if t=0 then 0 else
    max (singleTariff b j t) (if t=2 then (splitPrices b j).foldr max 0 else 0)
private theorem le_fold_max {v : ℕ} {L : List ℕ} (mem : v∈L) : v≤L.foldr max 0 := by
  induction L with
  | nil => simp at mem
  | cons a tail ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | m
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih m).trans (le_max_right _ _)
private theorem width_single (b j t : ℕ) (hp : 0<t) : singleTariff b j t≤widthCharge b j t := by
  unfold widthCharge
  rw [ite_eq_right (Nat.ne_of_gt hp)]
  exact le_max_left _ _
private theorem width_pair (b c j k : ℕ) (hj : 3≤j) (hk : 3≤k) (hb : j≤3*b) (hc : k≤3*c) :
    singleTariff b j 1+singleTariff c k 1≤widthCharge (b+c) (j+k) 2 := by
  unfold widthCharge
  rw [ite_eq_right (by decide : ¬(2 : ℕ)=0), ite_eq_left rfl]
  apply le_trans _ (le_max_right _ _)
  apply le_fold_max
  unfold splitPrices
  refine List.mem_flatMap.mpr ⟨b,List.mem_range.mpr (by omega),?_⟩
  refine List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  rw [show b+c-b=c by omega,show j+k-j=k by omega]
  rw [ite_eq_left ⟨hj,hb,hk,hc⟩]
private theorem checked_row (j : Fin 9) (t : Fin 3) :
    (List.range (lowDegreeCap j.val+1)).all (fun b=>decide
      (1≤t.val → 3*t.val≤j.val → j.val≤3*b → widthCharge b j.val t.val≤retainedTariff b j.val t.val)) = true := by
  fin_cases j <;> fin_cases t <;> decide +kernel
private theorem width_checked {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    widthCharge b j t≤retainedTariff b j t := by
  have inj : t<3 := by omega
  have h := List.all_eq_true.mp (checked_row ⟨j,by omega⟩ ⟨t,inj⟩)
    b (List.mem_range.mpr (Nat.lt_succ_of_le hb))
  exact of_decide_eq_true h ht hj hv
theorem retained_family_fee (n : ℕ) (a : Fin n→Shape) (hv : ∀ i,Valid (a i))
    (hj : (∑ i,(a i).j)≤8) (hb : (∑ i,(a i).b) ≤ lowDegreeCap (∑ i,(a i).j)) :
    (∑ i,fatPrice (a i)) ≤ retainedTariff (∑ i,(a i).b) (∑ i,(a i).j) (∑ i,(a i).t) := by
  have hsum : 3*(∑ i,(a i).t)≤∑ i,(a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _=>(hv i).2.1
  have hn' : n≤∑ i,(a i).t := calc
    n = ∑ _ : Fin n,1 := by simp
    _ ≤ ∑ i,(a i).t := sum_le_sum fun i _=>(hv i).1
  have hn : n≤2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    have one := hv 0
    have eq : a 0=⟨(a 0).b,(a 0).j,(a 0).t⟩ := by cases a 0; rfl
    conv_lhs => rw [eq]
    exact (single_price one.1 one.2.1 hj one.2.2 hb).trans
      ((width_single _ _ _ one.1).trans (width_checked one.1 one.2.1 hj one.2.2 hb))
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 : (a 0).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i=⟨(a i).b,(a i).j,(a i).t⟩ := by cases a i; rfl
    have shape0 : a 0=⟨(a 0).b,(a 0).j,1⟩ :=
      (he 0).trans (congrArg (fun t=>(⟨(a 0).b,(a 0).j,t⟩ : Shape)) ht0)
    have shape1 : a 1=⟨(a 1).b,(a 1).j,1⟩ :=
      (he 1).trans (congrArg (fun t=>(⟨(a 1).b,(a 1).j,t⟩ : Shape)) ht1)
    have hj0 : 3≤(a 0).j := by simpa only [ht0,Nat.mul_one] using (hv 0).2.1
    have hj1 : 3≤(a 1).j := by simpa only [ht1,Nat.mul_one] using (hv 1).2.1
    have j0hi : (a 0).j≤5 := by omega
    have j1hi : (a 1).j≤5 := by omega
    have totalB : (a 0).b+(a 1).b≤17 := by
      apply hb.trans
      have eq : (a 0).j+(a 1).j=6 ∨ (a 0).j+(a 1).j=7 ∨ (a 0).j+(a 1).j=8 := by omega
      rcases eq with eq | eq | eq <;> rw [eq] <;> decide
    have below (j : ℕ) (lo : 3≤j) (hi : j≤5) : 17≤lowDegreeCap j := by
      interval_cases j <;> decide
    have p0 := single_price (b:=(a 0).b) (t:=1) (by decide) (by simpa using hj0) (by omega)
      (hv 0).2.2 ((by omega : (a 0).b≤17).trans (below _ hj0 j0hi))
    have p1 := single_price (b:=(a 1).b) (t:=1) (by decide) (by simpa using hj1) (by omega)
      (hv 1).2.2 ((by omega : (a 1).b≤17).trans (below _ hj1 j1hi))
    rw [←shape0] at p0
    rw [←shape1] at p1
    have h := width_pair (a 0).b (a 1).b (a 0).j (a 1).j hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [ht0,ht1]
    exact (Nat.add_le_add p0 p1).trans (h.trans (width_checked (by decide) (by omega) hj (by
      have := (hv 0).2.2; have := (hv 1).2.2; omega) hb))
#print axioms retained_family_fee
end Lower6960.Low

end
end Merged_R6960Low6960RetainedFees

-- merged module R6960Low6960Width
section Merged_R6960Low6960Width

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.Low
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6960Retained (Box combined)
open Lower6960.Low (lowDegreeCap)
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators

theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ lowDegreeCap r.j := by
  have hjl : 3≤r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 ∨ r.j=8 := by omega
  rcases hj with hj | hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [lowDegreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.2 (by omega)

/-- The retained factors selected by the actual primary bank spend the
finite charge for their exact total width, before the positive-order allocation. -/
theorem Inventory.retained_charge {Γ : Finset K} {s : K→(Polynomial K)} (d : Inventory Γ s) :
    let r := combined (fun i=>shape (d.factor i)) d.zeros
    (∑ i∈d.zeros,fatPrice (shape (d.factor i))) ≤ retainedTariff r.b r.j r.t := by
  let q i := shape (d.factor i)
  let r := combined q d.zeros
  change (∑ i∈d.zeros,fatPrice (q i)) ≤ retainedTariff r.b r.j r.t
  by_cases empty : d.zeros=∅
  · simp [empty,r,combined,P3_6_8.shapeSum_empty,zeroShape,retainedTariff,retainedTariffs]
  · have box := (d.retained.resolve_left empty).1
    have hv : Valid r := (P3_6_8.shapeSum_valid_or_empty d.fits.1 d.zeros).resolve_left empty
    let e := d.zeros.equivFin.symm
    let ar : Fin d.zeros.card→Shape := fun i=>q (e i).val
    have sums (g : Shape→ℕ) : (∑ i,g (ar i)) = ∑ i∈d.zeros,g (q i) := by
      rw [←sum_attach d.zeros (fun i=>g (q i))]
      exact Fintype.sum_equiv e _ _ (fun _=>rfl)
    have hj : (∑ i,(ar i).j)≤8 := by rw [sums]; exact box.2.1
    have hb : (∑ i,(ar i).b)≤lowDegreeCap (∑ i,(ar i).j) := by
      rw [sums,sums]
      exact degree_bound hv box
    have h := retained_family_fee d.zeros.card ar (fun i=>d.fits.1 (e i).val) hj hb
    rw [sums,sums,sums,sums] at h
    exact h

#print axioms Inventory.retained_charge
end Lower6960.Low

end
end Merged_R6960Low6960Width

-- merged module R6960Low6960Prices
section Merged_R6960Low6960Prices

set_option Elab.async false
namespace Low6960Prices
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement := Lower6960.Low.agreement
abbrev physicalDegree := Lower6960.Low.physicalDegree
abbrev errors := Lower6960.Low.errors
abbrev incidenceGap := Lower6960.Low.incidenceGap
abbrev taylorLength := Lower6960.Low.taylorLength
abbrev anchorCutoff := Lower6960.Low.anchorCutoff
abbrev primaryCutoff := Lower6960.Low.primaryCutoff
def primaryBox : Shape := ⟨4012,1650,550⟩
abbrev layerWidth := Lower6960.Low.layerWidth
abbrev layerNeed := Lower6960.Low.need
abbrev symbolCount := Final50Price.symbolCount
abbrev TrueWeightLE := @Lower6960.Low.TrueWeightLE
abbrev LayerBudget := @Lower6960.Low.LayerBudget
abbrev remaining := Final50Price.remaining
abbrev Messages := Lower6960.Low.Messages
abbrev SmallFactor := Lower6960.Low.SmallFactor
abbrev LowerRow := Lower6960.Low.LowerRow
abbrev ProperCut := Lower6960.Low.ProperCut
abbrev ActiveFits := Final50Price.ActiveFits
abbrev Fits := @Lower6960.Low.Fits
abbrev fullCap := Lower6960.Low.fullCap
def lowerWidth (top : ℕ) : ℕ := 136-top
def lowerIndex (top : ℕ) : ℕ := 57-3*top
def lowerTop (top : ℕ) : ℕ := lowerIndex top/2
abbrev fatPrice := Lower6960.Low.fatPrice
abbrev FatEquations := Low6960Fat.FatEquations
abbrev Holds := Low6960Fat.Holds
abbrev fatOrder := Lower6960.Low.fatOrder
abbrev divisorOrder := Lower6960.Low.divisorOrder
abbrev isolatedOrder := Lower6960.Low.isolatedOrder
abbrev commonBox := Low6960Fat.commonBox
abbrev resultantBox := Low6960Fat.resultantBox
abbrev linearChart := Lower6960.Low.linearChart

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  Lower6960.Low.Messages.mono h hΔ

def lowerCap : ℕ → ℕ
  | 0 => 28934195010681851
  | 1 => 26144967484014750
  | 2 => 23484005213084631
  | 3 => 20954019640306880
  | 4 => 18556671643740158
  | 5 => 16294555828689425
  | 6 => 14169442943237300
  | 7 => 12183823564560699
  | 8 => 10339565297203618
  | 9 => 8639067908357704
  | 10 => 7084282436305361
  | 11 => 5677531465556135
  | 12 => 4420835636247467
  | 13 => 3316454386670376
  | 14 => 2366463717773566
  | _ => 0

def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l K
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, Holds E (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

end
end Low6960Prices

end Merged_R6960Low6960Prices

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone
set_option Elab.async false
section
namespace Low6960Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    Low6960Prices.surfaceNumerator32 p q ≤ Low6960Prices.surfaceNumerator32 p' q := by
  let L := Low6960Prices.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : Low6960Prices.physicalPriceOld x l ≤ Low6960Prices.physicalPriceOld y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6960Prices.primaryBox
  let L := Low6960Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6960Prices.errors hc) (Nat.mul_le_mul_left (2*Low6960Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6960Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end Low6960Monotone
end

namespace Low6960Monotone
open K1_13 (Shape)
open Low6960Prices (physicalPrice physicalPriceOld physicalPriceTilted physicalPriceActive physicalPriceWith)

theorem physicalPrice_le_old (x : Shape) (l K : ℕ) : physicalPrice x l K ≤ physicalPriceOld x l := by
  unfold physicalPrice
  split
  · split
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  · exact le_rfl

private theorem with_anti (a : Shape) (s : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPriceWith a u s ≤ physicalPriceWith a l s := by
  unfold physicalPriceWith
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _

theorem physicalPrice_anti (a : Shape) (K : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPrice a u K ≤ physicalPrice a l K := by
  have hold : physicalPriceOld a u ≤ physicalPriceOld a l := by
    unfold physicalPriceOld
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
  have hnew : physicalPriceTilted a u ≤ physicalPriceTilted a l := with_anti a _ hl h
  have hactive : physicalPriceActive a u K ≤ physicalPriceActive a l K := with_anti a _ hl h
  unfold physicalPrice
  split
  · split
    · exact min_le_min (min_le_min hold hnew) hactive
    · exact min_le_min hold hnew
  · exact hold
end Low6960Monotone

end Merged_R6960Low6960Monotone

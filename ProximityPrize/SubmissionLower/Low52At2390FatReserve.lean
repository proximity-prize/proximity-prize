import ProximityPrize.SubmissionLower.Low52At2390PriceBands

open scoped BigOperators

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace Low52At2390FatReserve
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open Low52At2390PriceCaps (charge)
open Low52At2390Price (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)

private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (Low52At2390Price.errors * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (Low52At2390Price.errors * mc + incidenceGap * mq) (32 * incidenceGap * length)
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
/-- Degree cap at each index of the retained product. -/
def degreeCap : ℕ → ℕ
  | 3 => 25
  | 4 => 23
  | 5 => 20
  | 6 => 16
  | 7 => 10
  | _ => 0

private theorem linear_3 : fatPrice ⟨25,3,1⟩ ≤ charge 25 3 1 := by decide +kernel
private theorem linear_4 : fatPrice ⟨23,4,1⟩ ≤ charge 23 4 1 := by decide +kernel
private theorem linear_5 : fatPrice ⟨20,5,1⟩ ≤ charge 20 5 1 := by decide +kernel
private theorem linear_6 : fatPrice ⟨16,6,1⟩ ≤ charge 16 6 1 := by decide +kernel
private theorem linear_7 : fatPrice ⟨10,7,1⟩ ≤ charge 10 7 1 := by decide +kernel

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
    · exact (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨25,3,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_3
    · exact (fatPrice_widen (x := ⟨b,4,1⟩) (y := ⟨23,4,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_4
    · exact (fatPrice_widen (x := ⟨b,5,1⟩) (y := ⟨20,5,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_5
    · exact (fatPrice_widen (x := ⟨b,6,1⟩) (y := ⟨16,6,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_6
    · exact (fatPrice_widen (x := ⟨b,7,1⟩) (y := ⟨10,7,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_7
  · have hcases : j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl
    · have h := hv.2.2
      change 6 ≤ 3 * b at h
      have hb₀ : 2 ≤ b := by omega
      change b ≤ 16 at hb
      interval_cases b <;> decide +kernel
    · have h := hv.2.2
      change 7 ≤ 3 * b at h
      have hb₀ : 3 ≤ b := by omega
      change b ≤ 10 at hb
      interval_cases b <;> decide +kernel

private theorem pair_width (b c j k width : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k)
    (hjk : j+k ≤ 7) (hb : j ≤ 3*b) (hc : k ≤ 3*c)
    (he : b+c = width) (hwidth : width ≤ degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge width (j+k) 2 := by
  have hj₁ : j ≤ 4 := by omega
  have hk₁ : k ≤ 4 := by omega
  have hb₀ : 1 ≤ b := by omega
  have hc₀ : 1 ≤ c := by omega
  have hw₀ : 2 ≤ width := by omega
  have hb₁ : b < width := by omega
  rw [show c = width-b by omega]
  interval_cases j <;> interval_cases k
  all_goals
    first
    | omega
    | norm_num [degreeCap] at hwidth
      interval_cases width <;> interval_cases b <;> first | omega | decide +kernel

/-- Two top-one retained factors use the reserve for their total index and degree. -/
theorem pair (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) (hjk : j + k ≤ 7)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge (b+c) (j+k) 2 :=
  pair_width b c j k _ hj hk hjk hb hc rfl hbc

/-- Reserve for the whole family of retained factors. -/
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

#print axioms single
#print axioms pair
#print axioms family
end Low52At2390FatReserve

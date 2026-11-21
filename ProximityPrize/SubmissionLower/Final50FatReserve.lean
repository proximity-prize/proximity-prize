import ProximityPrize.SubmissionLower.Final50Price

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
theorem chamber_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE x.chamber y.chamber :=
  ⟨max_le_max h.1 h.2.1.le, h.2⟩
theorem chart_widen (L : ℕ) {x y : Shape} (h : TotalLE x y) :
    TotalLE (chart L x) (chart L y) := by
  refine ⟨?_, by simp only [chart, h.2.1], by simp only [chart, h.2.1, h.2.2]⟩
  dsimp only [chart]
  rw [h.2.1]
  exact max_le_max
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h.1 _)) _) le_rfl
theorem fatChart_widen {x y : Shape} (h : TotalLE x y) :
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
theorem cut_widen {h H : Shape} (hh : TotalLE h H) :
    TotalLE (divisorCut h) (divisorCut H) := by
  refine ⟨?_, by simp only [divisorCut, hh.2.1], by simp only [divisorCut, hh.2.2]⟩
  dsimp only [divisorCut]
  rw [hh.2.1]
  exact max_le_max (max_le_max hh.1 le_rfl) le_rfl
theorem capped_index (b j t : ℕ) : IndexFits ⟨b, j, min t (j / 3)⟩ := by
  change 3 * min t (j / 3) ≤ j
  exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (by omega)
theorem fatChart_index (x : Shape) : IndexFits (fatChart x) := by
  unfold fatChart
  split <;> exact capped_index _ _ _
theorem cut_index {h : Shape} (hh : IndexFits h) : IndexFits (divisorCut h) := by
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
  | 4 => 22
  | 5 => 19
  | 6 => 15
  | 7 => 9
  | _ => 0

def charge (b j t : ℕ) : ℕ :=
  match t, j with
  | 1, 3 => 16501552670860878
  | 1, 4 => 28094873359840834
  | 1, 5 => 42519075367271737
  | 1, 6 => 49097136154047103
  | 1, 7 => 43238236495066495
  | 2, 6 => if b ≤ 6 then 75965195419107675 else if b ≤ 11 then 130245870501792300 else if b ≤ 13 then 152519255545335898 else 175215881615097912
  | 2, 7 => if b ≤ 5 then 137738665506187659 else 170357050644059833
  | _, _ => 0

theorem linear_3 : fatPrice ⟨25,3,1⟩ ≤ charge 25 3 1 := by decide +kernel
theorem linear_4 : fatPrice ⟨22,4,1⟩ ≤ charge 22 4 1 := by decide +kernel
theorem linear_5 : fatPrice ⟨19,5,1⟩ ≤ charge 19 5 1 := by decide +kernel
theorem linear_6 : fatPrice ⟨15,6,1⟩ ≤ charge 15 6 1 := by decide +kernel
theorem linear_7 : fatPrice ⟨9,7,1⟩ ≤ charge 9 7 1 := by decide +kernel
theorem quadratic_6a : fatPrice ⟨6,6,2⟩ ≤ charge 6 6 2 := by decide +kernel
theorem quadratic_6b : fatPrice ⟨11,6,2⟩ ≤ charge 11 6 2 := by decide +kernel
theorem quadratic_6c : fatPrice ⟨13,6,2⟩ ≤ charge 13 6 2 := by decide +kernel
theorem quadratic_6d : fatPrice ⟨15,6,2⟩ ≤ charge 15 6 2 := by decide +kernel
theorem quadratic_7a : fatPrice ⟨5,7,2⟩ ≤ charge 5 7 2 := by decide +kernel
theorem quadratic_7b : fatPrice ⟨9,7,2⟩ ≤ charge 9 7 2 := by decide +kernel

theorem charge6 (b : ℕ) (hb : b ≤ 15) :
    (b ≤ 6 ∧ charge b 6 2 = charge 6 6 2) ∨ (7 ≤ b ∧ b ≤ 11 ∧ charge b 6 2 = charge 11 6 2) ∨
    (12 ≤ b ∧ b ≤ 13 ∧ charge b 6 2 = charge 13 6 2) ∨ (14 ≤ b ∧ charge b 6 2 = charge 15 6 2) := by
  interval_cases b <;> simp [charge]

theorem charge7 (b : ℕ) :
    (b ≤ 5 ∧ charge b 7 2 = charge 5 7 2) ∨ (6 ≤ b ∧ charge b 7 2 = charge 9 7 2) := by
  by_cases h : b ≤ 5
  · exact Or.inl ⟨h, by simp [charge, h]⟩
  · exact Or.inr ⟨by omega, by simp [charge, h]⟩

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
    · exact (fatPrice_widen (x := ⟨b,4,1⟩) (y := ⟨22,4,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_4
    · exact (fatPrice_widen (x := ⟨b,5,1⟩) (y := ⟨19,5,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_5
    · exact (fatPrice_widen (x := ⟨b,6,1⟩) (y := ⟨15,6,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_6
    · exact (fatPrice_widen (x := ⟨b,7,1⟩) (y := ⟨9,7,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans linear_7
  · have hcases : j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl
    · change b ≤ 15 at hb
      rcases charge6 b hb with ⟨h1, e⟩ | ⟨_, h1, e⟩ | ⟨_, h1, e⟩ | ⟨_, e⟩
      · rw [e]; exact (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨6,6,2⟩) ⟨h1, rfl, rfl⟩ hindex).trans quadratic_6a
      · rw [e]; exact (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨11,6,2⟩) ⟨h1, rfl, rfl⟩ hindex).trans quadratic_6b
      · rw [e]; exact (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨13,6,2⟩) ⟨h1, rfl, rfl⟩ hindex).trans quadratic_6c
      · rw [e]; exact (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨15,6,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans quadratic_6d
    · change b ≤ 9 at hb
      rcases charge7 b with ⟨h1, e⟩ | ⟨_, e⟩
      · rw [e]; exact (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨5,7,2⟩) ⟨h1, rfl, rfl⟩ hindex).trans quadratic_7a
      · rw [e]; exact (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨9,7,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans quadratic_7b

theorem pair_width (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : (j + k = 6 ∧ (cap = 6 ∨ cap = 11 ∨ cap = 13 ∨ cap = 15)) ∨ (j + k = 7 ∧ (cap = 5 ∨ cap = 9)))
    (b c : ℕ) (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ cap) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge cap (j + k) 2 := by
  have hbmax : b ≤ 15 := by omega
  have hc' : c ≤ cap - b := by omega
  have h3j : IndexFits ⟨b,j,1⟩ := hjk.1
  have h3k : IndexFits ⟨c,k,1⟩ := hjk.2.1
  have hfee := fatPrice_widen (x := ⟨c,k,1⟩) (y := ⟨cap-b,k,1⟩) ⟨hc', rfl, rfl⟩ h3k
  refine (Nat.add_le_add_left hfee _).trans ?_
  have hj5 : j ≤ 4 := by omega
  have hk5 : k ≤ 4 := by omega
  have hc14 : cap ≤ 15 := by omega
  interval_cases j <;> interval_cases k <;> interval_cases cap <;> interval_cases b <;>
    first | omega | decide +kernel

/-- Two top-one retained factors use the reserve for their total index and degree. -/
theorem pair (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) (hjk : j + k ≤ 7)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge (b+c) (j+k) 2 := by
  have hcases : j + k = 6 ∨ j + k = 7 := by omega
  rcases hcases with h | h
  · have h15 : b + c ≤ 15 := by simpa only [h, degreeCap] using hbc
    rcases charge6 (b+c) h15 with ⟨h1, e⟩ | ⟨_, h1, e⟩ | ⟨_, h1, e⟩ | ⟨_, e⟩
    · have hh := pair_width j k 6 ⟨hj, hk, hjk⟩ (Or.inl ⟨h, by decide⟩) b c hb hc h1
      rw [h] at hh ⊢; rw [e]; exact hh
    · have hh := pair_width j k 11 ⟨hj, hk, hjk⟩ (Or.inl ⟨h, by decide⟩) b c hb hc h1
      rw [h] at hh ⊢; rw [e]; exact hh
    · have hh := pair_width j k 13 ⟨hj, hk, hjk⟩ (Or.inl ⟨h, by decide⟩) b c hb hc h1
      rw [h] at hh ⊢; rw [e]; exact hh
    · have hh := pair_width j k 15 ⟨hj, hk, hjk⟩ (Or.inl ⟨h, by decide⟩) b c hb hc h15
      rw [h] at hh ⊢; rw [e]; exact hh
  · have h9 : b + c ≤ 9 := by simpa only [h, degreeCap] using hbc
    rcases charge7 (b+c) with ⟨h1, e⟩ | ⟨_, e⟩
    · have hh := pair_width j k 5 ⟨hj, hk, hjk⟩ (Or.inr ⟨h, by decide⟩) b c hb hc h1
      rw [h] at hh ⊢; rw [e]; exact hh
    · have hh := pair_width j k 9 ⟨hj, hk, hjk⟩ (Or.inr ⟨h, by decide⟩) b c hb hc h9
      rw [h] at hh ⊢; rw [e]; exact hh

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

end Final50FatReserve

import ProximityPrize.SubmissionLower.K1AChild13C8At180255
set_option Elab.async false

/-! `K1A_13_8.c2 : Bellman zeroShape 224203454802083722` at A' = 180255 (need 25902203913876).
Port of K1_13_8_2 (Fast051.lean, 12b4b15d) by research/proximity-6916/port_k1a_c13_8_2.py.
* thresholds: ⟨118,48,58⟩ -> ⟨120,48,58⟩ (zeroMass(119,48) at order 57 is not below need');
* prices: `K1A_13.physicalPrice` at the A' orders, `indexBudget` with limit 224203454802083722 (46 bands);
* order certificate: `(l-1)*fastRemaining 0 0 + zeroMass b j < need` with the exact zeroMass, made monotone by
  `zeroMass_anti` (official c1 `K1_13_8_1.proof` + `remaining_anti`). The official upperMass/correction bound
  is too weak at need' (8/12 thresholds fail, c2_lean_threshold_check.json);
* `physical_mono` -> `K1A_13_8_5.physicalAt_mono 81889 46584`.
UNBUILT. -/

section PackSource_K1A_13_8_2Defs
set_option autoImplicit true
namespace K1A_13_8_2

open K1_13
open K1_13_8 (zeroShape fullCap Valid fastRemaining zeroMass availableMass sum_range_mono remaining_anti)
open K1_13_8_2 (allBelow allBelow_spec)
open K1A_13_8 (edgePrice edgePrice_anti)

def limit : ℕ := 224203454802083722

structure Threshold where
  b : ℕ
  j : ℕ
  l : ℕ

def thresholds : List Threshold :=
  [⟨120, 48, 58⟩, ⟨103, 43, 57⟩, ⟨67, 30, 52⟩, ⟨11, 16, 34⟩,
   ⟨4, 11, 17⟩, ⟨48, 4, 15⟩, ⟨5, 9, 7⟩, ⟨27, 6, 3⟩,
   ⟨19, 7, 2⟩, ⟨36, 4, 2⟩, ⟨9, 8, 2⟩, ⟨26, 6, 2⟩]

def orderFor (b j : ℕ) : List Threshold → ℕ
  | [] => 1
  | s :: rest =>
      max (if s.b ≤ b ∧ s.j ≤ j then s.l else 1) (orderFor b j rest)

def orderAt (x : Shape) : ℕ := orderFor x.b x.j thresholds

def potential (x : Shape) : ℕ := limit * (48 - x.j) / 48

def indexBudget (j : ℕ) : ℕ := limit * j / 48

end K1A_13_8_2
end PackSource_K1A_13_8_2Defs

section PackSource_K1A_13_8_2Prices
set_option autoImplicit true
namespace K1A_13_8_2

open K1_13
open K1_13_8 (zeroShape fullCap Valid fastRemaining zeroMass availableMass sum_range_mono remaining_anti)
open K1_13_8_2 (allBelow allBelow_spec)
open K1A_13_8 (edgePrice edgePrice_anti)

private def peak (b j : ℕ) : Shape := ⟨b, j, min 10 (j / 3)⟩

/-- For each index, check the right end of each constant-order degree interval. -/
private def endpoint (b j : ℕ) : Prop :=
  b = 120 ∨ orderAt (peak b j) ≠ orderAt (peak (b + 1) j)

private instance (b j : ℕ) : Decidable (endpoint b j) := by unfold endpoint; infer_instance

private def peakCheck (b j : ℕ) : Bool :=
  if j ≤ 3 * b ∧ endpoint b j then
    decide (K1A_13.physicalPrice (peak b j) (orderAt (peak b j)) ≤ indexBudget j)
  else true

private def priceBand (start count : ℕ) : Bool :=
  allBelow (fun i => allBelow (fun b => peakCheck b (start + i)) 121) count

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Extend a checked band by a single index, keeping the previous rows opaque. -/
private theorem priceBand_succ (start count : ℕ)
    (prev : priceBand start count = true)
    (row : allBelow (fun b => peakCheck b (start + count)) 121 = true) :
    priceBand start (count + 1) = true :=
  Bool.and_eq_true_iff.mpr ⟨row, prev⟩

private theorem pricesThrough3 : priceBand 3 1 = true :=
  priceBand_succ 3 0 rfl (by decide +kernel)

private theorem pricesThrough4 : priceBand 3 2 = true :=
  priceBand_succ 3 1 pricesThrough3 (by decide +kernel)

private theorem pricesThrough5 : priceBand 3 3 = true :=
  priceBand_succ 3 2 pricesThrough4 (by decide +kernel)

private theorem pricesThrough6 : priceBand 3 4 = true :=
  priceBand_succ 3 3 pricesThrough5 (by decide +kernel)

private theorem pricesThrough7 : priceBand 3 5 = true :=
  priceBand_succ 3 4 pricesThrough6 (by decide +kernel)

private theorem pricesThrough8 : priceBand 3 6 = true :=
  priceBand_succ 3 5 pricesThrough7 (by decide +kernel)

private theorem pricesThrough9 : priceBand 3 7 = true :=
  priceBand_succ 3 6 pricesThrough8 (by decide +kernel)

private theorem pricesThrough10 : priceBand 3 8 = true :=
  priceBand_succ 3 7 pricesThrough9 (by decide +kernel)

private theorem pricesThrough11 : priceBand 3 9 = true :=
  priceBand_succ 3 8 pricesThrough10 (by decide +kernel)

private theorem pricesThrough12 : priceBand 3 10 = true :=
  priceBand_succ 3 9 pricesThrough11 (by decide +kernel)

private theorem pricesThrough13 : priceBand 3 11 = true :=
  priceBand_succ 3 10 pricesThrough12 (by decide +kernel)

private theorem pricesThrough14 : priceBand 3 12 = true :=
  priceBand_succ 3 11 pricesThrough13 (by decide +kernel)

private theorem pricesThrough15 : priceBand 3 13 = true :=
  priceBand_succ 3 12 pricesThrough14 (by decide +kernel)

private theorem pricesThrough16 : priceBand 3 14 = true :=
  priceBand_succ 3 13 pricesThrough15 (by decide +kernel)

private theorem pricesThrough17 : priceBand 3 15 = true :=
  priceBand_succ 3 14 pricesThrough16 (by decide +kernel)

private theorem pricesThrough18 : priceBand 3 16 = true :=
  priceBand_succ 3 15 pricesThrough17 (by decide +kernel)

private theorem pricesThrough19 : priceBand 3 17 = true :=
  priceBand_succ 3 16 pricesThrough18 (by decide +kernel)

private theorem pricesThrough20 : priceBand 3 18 = true :=
  priceBand_succ 3 17 pricesThrough19 (by decide +kernel)

private theorem pricesThrough21 : priceBand 3 19 = true :=
  priceBand_succ 3 18 pricesThrough20 (by decide +kernel)

private theorem pricesThrough22 : priceBand 3 20 = true :=
  priceBand_succ 3 19 pricesThrough21 (by decide +kernel)

private theorem pricesThrough23 : priceBand 3 21 = true :=
  priceBand_succ 3 20 pricesThrough22 (by decide +kernel)

private theorem pricesThrough24 : priceBand 3 22 = true :=
  priceBand_succ 3 21 pricesThrough23 (by decide +kernel)

private theorem pricesThrough25 : priceBand 3 23 = true :=
  priceBand_succ 3 22 pricesThrough24 (by decide +kernel)

private theorem pricesThrough26 : priceBand 3 24 = true :=
  priceBand_succ 3 23 pricesThrough25 (by decide +kernel)

private theorem pricesThrough27 : priceBand 3 25 = true :=
  priceBand_succ 3 24 pricesThrough26 (by decide +kernel)

private theorem pricesThrough28 : priceBand 3 26 = true :=
  priceBand_succ 3 25 pricesThrough27 (by decide +kernel)

private theorem pricesThrough29 : priceBand 3 27 = true :=
  priceBand_succ 3 26 pricesThrough28 (by decide +kernel)

private theorem pricesThrough30 : priceBand 3 28 = true :=
  priceBand_succ 3 27 pricesThrough29 (by decide +kernel)

private theorem pricesThrough31 : priceBand 3 29 = true :=
  priceBand_succ 3 28 pricesThrough30 (by decide +kernel)

private theorem pricesThrough32 : priceBand 3 30 = true :=
  priceBand_succ 3 29 pricesThrough31 (by decide +kernel)

private theorem pricesThrough33 : priceBand 3 31 = true :=
  priceBand_succ 3 30 pricesThrough32 (by decide +kernel)

private theorem pricesThrough34 : priceBand 3 32 = true :=
  priceBand_succ 3 31 pricesThrough33 (by decide +kernel)

private theorem pricesThrough35 : priceBand 3 33 = true :=
  priceBand_succ 3 32 pricesThrough34 (by decide +kernel)

private theorem pricesThrough36 : priceBand 3 34 = true :=
  priceBand_succ 3 33 pricesThrough35 (by decide +kernel)

private theorem pricesThrough37 : priceBand 3 35 = true :=
  priceBand_succ 3 34 pricesThrough36 (by decide +kernel)

private theorem pricesThrough38 : priceBand 3 36 = true :=
  priceBand_succ 3 35 pricesThrough37 (by decide +kernel)

private theorem pricesThrough39 : priceBand 3 37 = true :=
  priceBand_succ 3 36 pricesThrough38 (by decide +kernel)

private theorem pricesThrough40 : priceBand 3 38 = true :=
  priceBand_succ 3 37 pricesThrough39 (by decide +kernel)

private theorem pricesThrough41 : priceBand 3 39 = true :=
  priceBand_succ 3 38 pricesThrough40 (by decide +kernel)

private theorem pricesThrough42 : priceBand 3 40 = true :=
  priceBand_succ 3 39 pricesThrough41 (by decide +kernel)

private theorem pricesThrough43 : priceBand 3 41 = true :=
  priceBand_succ 3 40 pricesThrough42 (by decide +kernel)

private theorem pricesThrough44 : priceBand 3 42 = true :=
  priceBand_succ 3 41 pricesThrough43 (by decide +kernel)

private theorem pricesThrough45 : priceBand 3 43 = true :=
  priceBand_succ 3 42 pricesThrough44 (by decide +kernel)

private theorem pricesThrough46 : priceBand 3 44 = true :=
  priceBand_succ 3 43 pricesThrough45 (by decide +kernel)

private theorem pricesThrough47 : priceBand 3 45 = true :=
  priceBand_succ 3 44 pricesThrough46 (by decide +kernel)

private theorem allPrices : priceBand 3 46 = true :=
  priceBand_succ 3 45 pricesThrough47 (by decide +kernel)

private theorem priceBand_spec {start count b j : ℕ}
    (h : priceBand start count = true) (hlo : start ≤ j) (hhi : j < start + count)
    (hb : b ≤ 120) (hshape : j ≤ 3 * b) (he : endpoint b j) :
    K1A_13.physicalPrice (peak b j) (orderAt (peak b j)) ≤ indexBudget j := by
  have hc := allBelow_spec (allBelow_spec h (k := j - start) (by omega)) (k := b) (by omega)
  rwa [Nat.add_sub_of_le hlo, peakCheck, ite_eq_left ⟨hshape, he⟩, decide_eq_true_eq] at hc

private theorem peak_bound (b j : ℕ) (hb : b ≤ 120) (hshape : j ≤ 3 * b)
    (hend : ∀ k ≤ 120, j ≤ 3 * k → endpoint k j →
      K1A_13.physicalPrice (peak k j) (orderAt (peak k j)) ≤ indexBudget j) :
    K1A_13.physicalPrice (peak b j) (orderAt (peak b j)) ≤ indexBudget j := by
  induction hb using Nat.decreasingInduction with
  | self => exact hend _ le_rfl hshape (Or.inl rfl)
  | of_succ b hb ih =>
    by_cases he : endpoint b j
    · exact hend b (by omega) hshape he
    · have horder : orderAt (peak b j) = orderAt (peak (b + 1) j) := by
        by_contra h
        exact he (Or.inr h)
      have ht : 3 * (peak b j).t ≤ j := by dsimp [peak]; omega
      have hmono : InBox (peak b j) (peak (b + 1) j) := ⟨by dsimp [peak]; omega, le_rfl, le_rfl⟩
      rw [horder]
      exact (K1A_13_8_5.physicalAt_mono 81889 46584 hmono ht ht _).trans (ih (by omega))


theorem price_upper {a : Shape} (ha : Valid a) (hbox : InBox a fullCap) :
    K1A_13.physicalPrice a (orderAt a) ≤ indexBudget a.j := by
  have hj : 3 ≤ a.j := (Nat.mul_le_mul_left 3 ha.1).trans ha.2.1
  have hmax : a.j ≤ 48 := hbox.2.1
  have ht : a.t ≤ (peak a.b a.j).t :=
    le_min hbox.2.2 ((Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
      (by simpa [Nat.mul_comm] using ha.2.1))
  have htop : 3 * (peak a.b a.j).t ≤ a.j := by dsimp [peak]; omega
  have hmono : InBox a (peak a.b a.j) := ⟨le_rfl, le_rfl, ht⟩
  have horder : orderAt a = orderAt (peak a.b a.j) := rfl
  rw [horder]
  exact (K1A_13_8_5.physicalAt_mono 81889 46584 hmono ha.2.1 htop _).trans <|
    peak_bound _ _ hbox.1 ha.2.2 fun b hb hvalid he =>
      priceBand_spec allPrices hj (by omega) hb hvalid he


end K1A_13_8_2
end PackSource_K1A_13_8_2Prices

section PackSource_K1A_13_8_2Order
set_option autoImplicit true
namespace K1A_13_8_2

open K1_13
open K1_13_8 (zeroShape fullCap Valid fastRemaining zeroMass availableMass sum_range_mono remaining_anti)
open K1_13_8_2 (allBelow allBelow_spec)
open K1A_13_8 (edgePrice edgePrice_anti)
open scoped BigOperators

/-- zeroMass is antitone in both budgets (from the exact symbol count c1). -/
theorem zeroMass_anti (hcount : ∀ b j, remaining b j = fastRemaining b j) {b j b₀ j₀ : ℕ}
    (hj₀ : 0 < j₀) (hb : b₀ ≤ b) (hj : j₀ ≤ j) : zeroMass b j ≤ zeroMass b₀ j₀ := by
  unfold zeroMass
  apply sum_range_mono (Nat.div_le_div_left hj hj₀)
  intro k _
  rw [← hcount, ← hcount]
  exact remaining_anti (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)

private def thresholdCheck (s : Threshold) : Bool :=
  decide (0 < s.j ∧ (s.l - 1) * fastRemaining 0 0 + zeroMass s.b s.j < K1A_13_8.need)

section
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem orderThreshold120_48 : thresholdCheck ⟨120, 48, 58⟩ = true := by
  decide +kernel

private theorem orderThreshold103_43 : thresholdCheck ⟨103, 43, 57⟩ = true := by
  decide +kernel

private theorem orderThreshold67_30 : thresholdCheck ⟨67, 30, 52⟩ = true := by
  decide +kernel

private theorem orderThreshold11_16 : thresholdCheck ⟨11, 16, 34⟩ = true := by
  decide +kernel

private theorem orderThreshold4_11 : thresholdCheck ⟨4, 11, 17⟩ = true := by
  decide +kernel

private theorem orderThreshold48_4 : thresholdCheck ⟨48, 4, 15⟩ = true := by
  decide +kernel

private theorem orderThreshold5_9 : thresholdCheck ⟨5, 9, 7⟩ = true := by
  decide +kernel

private theorem orderThreshold27_6 : thresholdCheck ⟨27, 6, 3⟩ = true := by
  decide +kernel

private theorem orderThreshold19_7 : thresholdCheck ⟨19, 7, 2⟩ = true := by
  decide +kernel

private theorem orderThreshold36_4 : thresholdCheck ⟨36, 4, 2⟩ = true := by
  decide +kernel

private theorem orderThreshold9_8 : thresholdCheck ⟨9, 8, 2⟩ = true := by
  decide +kernel

private theorem orderThreshold26_6 : thresholdCheck ⟨26, 6, 2⟩ = true := by
  decide +kernel

end

private theorem thresholdChecks : thresholds.all thresholdCheck = true := by
  simp only [thresholds, List.all_cons, List.all_nil, Bool.true_and,
    orderThreshold120_48, orderThreshold103_43, orderThreshold67_30, orderThreshold11_16, orderThreshold4_11, orderThreshold48_4, orderThreshold5_9, orderThreshold27_6, orderThreshold19_7, orderThreshold36_4, orderThreshold9_8, orderThreshold26_6]

private theorem orderFor_select (b j : ℕ) (ss : List Threshold) :
    1 ≤ orderFor b j ss ∧
    (orderFor b j ss = 1 ∨ ∃ s ∈ ss, s.b ≤ b ∧ s.j ≤ j ∧ orderFor b j ss = s.l) := by
  induction ss with
  | nil => simp [orderFor]
  | cons s ss ih =>
    unfold orderFor
    let p := if s.b ≤ b ∧ s.j ≤ j then s.l else 1
    change 1 ≤ max p (orderFor b j ss) ∧
      (max p (orderFor b j ss) = 1 ∨ ∃ q ∈ s :: ss,
        q.b ≤ b ∧ q.j ≤ j ∧ max p (orderFor b j ss) = q.l)
    refine ⟨ih.1.trans (le_max_right _ _), ?_⟩
    rcases le_total p (orderFor b j ss) with h | h
    · rw [max_eq_right h]
      rcases ih.2 with h1 | ⟨q, hq, hb, hj, hl⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hb, hj, hl⟩
    · rw [max_eq_left h]
      by_cases hbox : s.b ≤ b ∧ s.j ≤ j
      · exact Or.inr ⟨s, List.mem_cons_self, hbox.1, hbox.2, ite_eq_left hbox⟩
      · exact Or.inl (ite_eq_right hbox)

private theorem orderFor_mono {b b' j j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ss : List Threshold) :
    orderFor b j ss ≤ orderFor b' j' ss := by
  induction ss with
  | nil => exact le_rfl
  | cons s ss ih =>
    unfold orderFor
    by_cases h : s.b ≤ b ∧ s.j ≤ j
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.trans hb, h.2.trans hj⟩]
      exact max_le_max le_rfl ih
    · rw [ite_eq_right h, max_eq_right (orderFor_select b j ss).1]
      exact ih.trans (le_max_right _ _)

theorem orderAt_pos (x : Shape) : 0 < orderAt x := (orderFor_select x.b x.j thresholds).1

theorem orderAt_mono {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    orderAt x ≤ orderAt y := orderFor_mono hb hj thresholds

theorem orderAt_certified (x : Shape) (hb : x.b ≤ 120) (hj : x.j ≤ 48) :
    orderAt x = 1 ∨ availableMass zeroShape x (orderAt x - 1) < K1A_13_8.need := by
  rcases (orderFor_select x.b x.j thresholds).2 with he | ⟨s, hs, hsb, hsj, he⟩
  · exact Or.inl he
  · have hcheck := of_decide_eq_true (List.all_eq_true.mp thresholdChecks s hs)
    have hm := zeroMass_anti K1_13_8_1.proof hcheck.1 hsb hsj
    have hlt := hcheck.2
    change orderAt x = s.l at he
    right
    rw [he]
    simp only [availableMass, zeroShape, Nat.zero_add, Nat.mul_zero, ite_true]
    change (s.l - 1) * fastRemaining 0 0 + zeroMass x.b x.j < K1A_13_8.need
    omega

end K1A_13_8_2
end PackSource_K1A_13_8_2Order

section PackSource_K1A_13_8_2Proof
set_option autoImplicit true
namespace K1A_13_8_2

open K1_13
open K1_13_8 (zeroShape fullCap Valid fastRemaining zeroMass availableMass sum_range_mono remaining_anti)
open K1_13_8_2 (allBelow allBelow_spec)
open K1A_13_8 (edgePrice edgePrice_anti)

private theorem edge_le_physical (a : Shape) (l : ℕ) : edgePrice a l ≤ K1A_13.physicalPrice a l := by
  unfold edgePrice
  split
  · exact min_le_left _ _
  · exact le_rfl

private theorem zero_plus (x : Shape) : zeroShape.plus x = x := by
  cases x
  simp [zeroShape, Shape.plus]

theorem proof : K1A_13_8.c2 := by
  refine ⟨potential, orderAt, by decide, ?_, ?_⟩
  · intro x _ hx
    rw [zero_plus] at hx
    exact ⟨orderAt_pos x, orderAt_certified x hx.1 hx.2.1⟩
  · intro y a _ ha hbox
    let x := y.plus a
    have hcap : InBox x fullCap := by simpa only [zero_plus] using hbox
    have haBox : InBox a x := ⟨Nat.le_add_left _ _, Nat.le_add_left _ _, Nat.le_add_left _ _⟩
    have hb : InBox a fullCap :=
      ⟨haBox.1.trans hcap.1, haBox.2.1.trans hcap.2.1, haBox.2.2.trans hcap.2.2⟩
    have hl := orderAt_mono haBox.1 haBox.2.1
    have hprice : edgePrice a (orderAt x) ≤ indexBudget a.j :=
      (edgePrice_anti a (orderAt_pos a) hl).trans
        ((edge_le_physical a _).trans (price_upper ha hb))
    have hidx : a.j + (48 - x.j) = 48 - y.j := by
      have h := hcap.2.1
      change _ + _ ≤ 48 at h
      dsimp [x, Shape.plus]
      omega
    calc
      edgePrice a (orderAt x) + potential x ≤ indexBudget a.j + potential x :=
        Nat.add_le_add_right hprice _
      _ ≤ potential y := by
        have hdiv : limit * a.j / 48 + limit * (48 - x.j) / 48 ≤
            (limit * a.j + limit * (48 - x.j)) / 48 := Nat.div_add_div_le_add_div
        rw [← Nat.mul_add, hidx] at hdiv
        exact hdiv


end K1A_13_8_2
end PackSource_K1A_13_8_2Proof

section PackSource_K1A_13_8C2Assembly
set_option autoImplicit true
namespace K1A_13_8

/-- `K1A_13.c8` with the A' c2 discharged; c3 and c4 remain. -/
theorem c8_of_c2 (h3 : c3) (h4 : c4) : K1A_13.c8 := c8_of K1A_13_8_2.proof h3 h4

end K1A_13_8
end PackSource_K1A_13_8C2Assembly

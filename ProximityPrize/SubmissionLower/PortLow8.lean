import ProximityPrize.SubmissionLower.PortLow7
set_option Elab.async false

section PackSource_P0_9_8Defs
set_option autoImplicit true
namespace P0_9_8

open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape fullCap availableMass)
open K1_13_8_2 (Threshold orderFor)

abbrev factorCap : ℕ := 214480139679075858
abbrev oneReserve : ℕ := 37000000000000000
abbrev twoReserve : ℕ := 97000000000000000

abbrev oneStart : Shape := ⟨1, 3, 1⟩
abbrev twoStart : Shape := ⟨2, 6, 2⟩

/-- Each empty-start threshold supplies an order on the quadrant above it. -/
def emptyThresholds : List Threshold :=
  [⟨107, 46, 60⟩, ⟨14, 41, 57⟩, ⟨61, 31, 56⟩, ⟨11, 13, 37⟩,
    ⟨9, 7, 13⟩, ⟨22, 4, 12⟩, ⟨3, 7, 8⟩]

def emptyOrder (x : Shape) : ℕ := orderFor x.b x.j emptyThresholds

/-- For a retained factor of top degree one, use only the positive index spend. -/
def oneOrder (x : Shape) : ℕ := if x.j ≤ 3 then 1 else (3 * x.j - 4) / 2

abbrev twoOrder : ℕ := 85

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (48 - r.j)

def edgePrice (a : Shape) (L : ℕ) : ℕ :=
  if FatEligible a then min (P0_9.physicalPrice a L) (P0_9.fatPrice a)
  else P0_9.physicalPrice a L

/-- The positive phase uses a reverse potential. Every intermediate state may stop. -/
def Bellman (r : Shape) (cap : ℕ) : Prop :=
  ∃ (B order : Shape → ℕ), B zeroShape ≤ cap ∧
    (∀ x, Valid x → InBox (r.plus x) fullCap →
      0 < order x ∧
        (order x = 1 ∨ availableMass r x (order x - 1) < P0_9.layerNeed)) ∧
    (∀ (y a : Shape), (y = zeroShape ∨ Valid y) → Valid a →
      InBox (r.plus (y.plus a)) fullCap →
      edgePrice a (order (y.plus a)) + B (y.plus a) ≤ B y)

end P0_9_8
end PackSource_P0_9_8Defs

section PackSource_P0_9_8Aux
set_option autoImplicit true
namespace P0_9_8

open K1_13 (Shape InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape fullCap availableMass layerTerm)
open K1_13_8_2 (Threshold orderFor)
open scoped BigOperators

theorem symbol_count : ∀ b j, remaining b j = K1_13_8.fastRemaining b j :=
  K1_13_8_1.proof

theorem edgePrice_anti (a : Shape) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    edgePrice a u ≤ edgePrice a l := by
  have hp : P0_9.physicalPrice a u ≤ P0_9.physicalPrice a l := by
    unfold P0_9.physicalPrice
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
  unfold edgePrice
  split <;> first | exact min_le_min hp le_rfl | exact hp

theorem edgePrice_le_physical (a : Shape) (l : ℕ) :
    edgePrice a l ≤ P0_9.physicalPrice a l := by
  unfold edgePrice
  split
  · exact min_le_left _ _
  · exact le_rfl

/-- Increasing the positive prefix only spends more at every layer. -/
theorem availableMass_anti_prefix {r y x : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j)
    (hb : y.b ≤ x.b) (hidx : y.j ≤ x.j) :
    availableMass r x L ≤ availableMass r y L := by
  let N := max (L + 1650 / (r.j + x.j)) (L + 1650 / (r.j + y.j))
  have hjx : 0 < r.j + x.j := by omega
  rw [← K1_13_8.availableMass_eq_sum symbol_count hr hjx (N := N) (le_max_left _ _),
    ← K1_13_8.availableMass_eq_sum symbol_count hr hj (N := N) (le_max_right _ _)]
  exact Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1 - L) hb) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1 - L) hidx) _)

-- Port the threshold selection argument from the light K1_13_8_2Order.
theorem orderFor_select (b j : ℕ) (ss : List Threshold) :
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

theorem orderFor_mono {b b' j j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ss : List Threshold) :
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

theorem oneOrder_pos (x : Shape) : 0 < oneOrder x := by
  unfold oneOrder
  split <;> omega

theorem oneOrder_mono {x y : Shape} (h : x.j ≤ y.j) : oneOrder x ≤ oneOrder y := by
  unfold oneOrder
  split <;> split <;> omega

/-- An index-linear potential turns single-factor charges into a prefix bound. -/
theorem bellman_of_budget (r : Shape) (cap : ℕ) (order : Shape → ℕ)
    (hpos : ∀ x, 0 < order x)
    (hmono : ∀ {a x}, a.b ≤ x.b → a.j ≤ x.j → order a ≤ order x)
    (horders : ∀ x, Valid x → InBox (r.plus x) fullCap →
      order x = 1 ∨ availableMass r x (order x - 1) < P0_9.layerNeed)
    (hprice : ∀ a, Valid a → InBox (r.plus a) fullCap →
      P0_9.physicalPrice a (order a) ≤ indexBudget r cap a.j) :
    Bellman r cap := by
  let B := fun y : Shape => indexBudget r cap (48 - r.j - y.j)
  refine ⟨B, order, ?_, fun x hx hb => ⟨hpos x, horders x hx hb⟩, ?_⟩
  · change cap * (48 - r.j - 0) / (48 - r.j) ≤ cap
    rw [Nat.sub_zero]
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm])
  · intro y a _ ha hbox
    let x := y.plus a
    have hb : InBox (r.plus a) fullCap :=
      ⟨(Nat.add_le_add_left (Nat.le_add_left a.b y.b) _).trans hbox.1,
        (Nat.add_le_add_left (Nat.le_add_left a.j y.j) _).trans hbox.2.1,
        (Nat.add_le_add_left (Nat.le_add_left a.t y.t) _).trans hbox.2.2⟩
    have hl := hmono (a := a) (x := x) (Nat.le_add_left _ _) (Nat.le_add_left _ _)
    have hfee := (edgePrice_anti a (hpos a) hl).trans
      ((edgePrice_le_physical a _).trans (hprice a ha hb))
    have hidx : r.j + (y.j + a.j) ≤ 48 := hbox.2.1
    have hbalance : a.j + (48 - r.j - x.j) = 48 - r.j - y.j := by
      change a.j + (48 - r.j - (y.j + a.j)) = 48 - r.j - y.j
      omega
    apply (Nat.add_le_add_right hfee (B x)).trans
    have hdiv : cap * a.j / (48 - r.j) + cap * (48 - r.j - x.j) / (48 - r.j) ≤
        (cap * a.j + cap * (48 - r.j - x.j)) / (48 - r.j) :=
      Nat.div_add_div_le_add_div
    rw [← Nat.mul_add, hbalance] at hdiv
    exact hdiv

end P0_9_8
end PackSource_P0_9_8Aux

section PackSource_P0_9_8Split
set_option autoImplicit true
namespace P0_9_8

open K1_13 (Shape Fits InBox FatEligible)
open K1_13_8 (Valid RetainedBox zeroShape fullCap availableMass layerTerm layerCount)
open K1_13_8_2 (Threshold orderFor)
open scoped BigOperators

/-- Fat fees within the enclosing box of feasible retained products. -/
def c1 : Prop :=
  ∀ a, Valid a → RetainedBox a →
    P0_9.fatPrice a ≤ (if a.t = 1 then oneReserve else 48500000000000000) * a.t

/-- Seven evaluations certify the order when nothing has been retained. -/
def c2 : Prop :=
  ∀ s ∈ emptyThresholds,
    availableMass zeroShape ⟨s.b, s.j, 0⟩ (s.l - 1) < P0_9.layerNeed

/-- A single positive fee uses at most its share of the total index budget. -/
def c3 : Prop :=
  ∀ a, Valid a → InBox (zeroShape.plus a) fullCap →
    P0_9.physicalPrice a (emptyOrder a) ≤ indexBudget zeroShape factorCap a.j

/-- With retained resource (1,3,1), drop the positive degree spend in the order test. -/
def c4 : Prop :=
  ∀ j : ℕ, 4 ≤ j → j ≤ 45 →
    availableMass oneStart ⟨0, j, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) < P0_9.layerNeed

/-- The paid index budget for one unit of retained top degree. -/
def c5 : Prop :=
  ∀ a, Valid a → InBox (oneStart.plus a) fullCap →
    P0_9.physicalPrice a (oneOrder a) ≤ indexBudget oneStart (factorCap - oneReserve) a.j

/-- One evaluation gives an order of at least 85 after two units of retained top degree. -/
def c6 : Prop :=
  availableMass twoStart ⟨0, 3, 0⟩ (twoOrder - 1) < P0_9.layerNeed

/-- The paid index budget for two units of retained top degree. -/
def c7 : Prop :=
  ∀ a, Valid a → InBox (twoStart.plus a) fullCap →
    P0_9.physicalPrice a twoOrder ≤ indexBudget twoStart (factorCap - twoReserve) a.j

private theorem empty_bellman (horder : c2) (hprice : c3) : Bellman zeroShape factorCap := by
  apply bellman_of_budget zeroShape factorCap emptyOrder
    (fun x => (orderFor_select x.b x.j emptyThresholds).1)
    (fun hb hj => orderFor_mono hb hj emptyThresholds) _ hprice
  intro x _ _
  rcases (orderFor_select x.b x.j emptyThresholds).2 with he | ⟨s, hs, hb, hj, he⟩
  · exact Or.inl he
  · have hj0 : 0 < s.j := by
      simp [emptyThresholds] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    right
    change emptyOrder x = s.l at he
    rw [he]
    exact (availableMass_anti_prefix (y := ⟨s.b, s.j, 0⟩)
      (Or.inl rfl) (by simpa [zeroShape] using hj0) hb hj).trans_lt (horder s hs)

private theorem one_bellman (horder : c4) (hprice : c5) :
    Bellman oneStart (factorCap - oneReserve) := by
  apply bellman_of_budget oneStart (factorCap - oneReserve) oneOrder oneOrder_pos
    (fun _ hj => oneOrder_mono hj) _ hprice
  intro x _ hx
  have hj : 3 + x.j ≤ 48 := hx.2.1
  by_cases hsmall : x.j ≤ 3
  · exact Or.inl (ite_eq_left hsmall)
  · have h := horder x.j (by omega) (by omega)
    exact Or.inr <| (availableMass_anti_prefix (x := x) (y := ⟨0, x.j, 0⟩)
      (Or.inr (by decide)) (by change 0 < 3 + x.j; omega)
      (Nat.zero_le x.b) le_rfl).trans_lt h

private theorem two_bellman (horder : c6) (hprice : c7) :
    Bellman twoStart (factorCap - twoReserve) := by
  apply bellman_of_budget twoStart (factorCap - twoReserve) (fun _ => twoOrder)
    (fun _ => by decide) (fun _ _ => le_rfl) _ hprice
  intro x hx _
  have hj : 3 ≤ x.j := (Nat.mul_le_mul_left 3 hx.1).trans hx.2.1
  exact Or.inr <| (availableMass_anti_prefix (y := ⟨0, 3, 0⟩)
    (Or.inr (by decide)) (by decide) (Nat.zero_le _) hj).trans_lt horder

private def shapeSum {ι : Type*} (a : ι → Shape) (s : Finset ι) : Shape :=
  ⟨∑ i ∈ s, (a i).b, ∑ i ∈ s, (a i).j, ∑ i ∈ s, (a i).t⟩

private theorem shapeSum_empty {ι : Type*} (a : ι → Shape) :
    shapeSum a ∅ = zeroShape := by simp [shapeSum, zeroShape]

private theorem shapeSum_insert {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {i : ι} {s : Finset ι} (hi : i ∉ s) :
    shapeSum a (insert i s) = (shapeSum a s).plus (a i) := by
  simp [shapeSum, Shape.plus, Finset.sum_insert hi, Nat.add_comm]

private theorem shapeSum_union {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {s t : Finset ι} (h : Disjoint s t) :
    shapeSum a (s ∪ t) = (shapeSum a s).plus (shapeSum a t) := by
  simp [shapeSum, Shape.plus, Finset.sum_union h]

private theorem shapeSum_mono {ι : Type*} (a : ι → Shape) {s t : Finset ι}
    (h : s ⊆ t) : InBox (shapeSum a s) (shapeSum a t) :=
  ⟨Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h⟩

private theorem inBox_trans {a b c : Shape} (hab : InBox a b) (hbc : InBox b c) :
    InBox a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

private theorem inBox_shapeSum {ι : Type*} (a : ι → Shape) {i : ι} {s : Finset ι}
    (hi : i ∈ s) : InBox (a i) (shapeSum a s) :=
  ⟨Finset.single_le_sum (f := fun i => (a i).b) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).j) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).t) (fun _ _ => Nat.zero_le _) hi⟩

private theorem shapeSum_valid_or_empty {ι : Type*} {a : ι → Shape}
    (ha : ∀ i, Valid (a i)) (s : Finset ι) :
    s = ∅ ∨ Valid (shapeSum a s) := by
  by_cases he : s.Nonempty
  · obtain ⟨i, hi⟩ := he
    refine Or.inr ⟨(ha i).1.trans (inBox_shapeSum a hi).2.2, ?_, ?_⟩
    · change 3 * (∑ i ∈ s, (a i).t) ≤ ∑ i ∈ s, (a i).j
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.1
    · change (∑ i ∈ s, (a i).j) ≤ 3 * ∑ i ∈ s, (a i).b
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.2
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp he)

private theorem spend_le {ι : Type*} [DecidableEq ι] [Fintype ι] {l : ι → ℕ}
    (f : ι → ℕ) {z s : Finset ι} {q d L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L) (hdisj : Disjoint z s)
    (hq : q ≤ ∑ i ∈ z, f i) :
    d * q + (d - L) * (∑ i ∈ s, f i) ≤ ∑ i, (d - l i) * f i := by
  calc
    _ ≤ d * (∑ i ∈ z, f i) + (d - L) * (∑ i ∈ s, f i) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
    _ = (∑ i ∈ z, d * f i) + ∑ i ∈ s, (d - L) * f i := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (∑ i ∈ z, (d - l i) * f i) + ∑ i ∈ s, (d - l i) * f i := by
      apply Nat.add_le_add
      · exact Finset.sum_le_sum fun i hi => by rw [hz i hi, Nat.sub_zero]
      · exact Finset.sum_le_sum fun i hi =>
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (hs i hi) _)
    _ = ∑ i ∈ z ∪ s, (d - l i) * f i := (Finset.sum_union hdisj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : P0_9.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (shapeSum a z)) :
    P0_9.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (shapeSum a s) L k := by
  have hcount : 1 + P0_9.primaryCutoff / P0_9.layerWidth ≤ layerCount := by decide
  refine hlayers.trans ((Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti ?_ ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono hcount)))
  · exact spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact spend_le (fun i => (a i).j) hz hs hdisj hq.2.1

private theorem retained_cost {ι : Type*} {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} (hretained : c1) (ha : ∀ i, Valid (a i)) (hbox : RetainedBox (shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ P0_9.fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤
      (if (shapeSum a z).t = 1 then oneReserve else 48500000000000000) *
        (shapeSum a z).t := by
  let r := shapeSum a z
  let rate : ℕ := if r.t = 1 then oneReserve else 48500000000000000
  change (∑ i ∈ z, cost i) ≤ rate * ∑ i ∈ z, (a i).t
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hle : InBox (a i) r := inBox_shapeSum a hi
  have hsmall := K1_13_8.retainedBox_down hle hbox
  have hcheap : FatEligible (a i) :=
    ⟨hsmall.1.trans (by decide), hsmall.2.1.trans (by decide)⟩
  refine (hfat i hcheap).trans ((hretained _ (ha i) hsmall).trans ?_)
  apply Nat.mul_le_mul_right
  have ht := (ha i).1
  have hti := hle.2.2
  by_cases h : r.t = 1
  · have hai : (a i).t = 1 := by omega
    simp [rate, h, hai]
  · split <;> simp [rate, h, oneReserve]

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) (h7 : c7) : P0_9.c8 := by
  intro n a l cost hfits hlayers hphys hfat
  let z := Finset.univ.filter (fun i => l i = 0)
  let pos := Finset.univ.filter (fun i => ¬ l i = 0)
  let r := shapeSum a z
  have ha (i : Fin n) : Valid (a i) := hfits.1 i
  have hz (i : Fin n) (hi : i ∈ z) : l i = 0 := (Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ (q : Shape) (cap : ℕ), InBox q r ∧ (q = zeroShape ∨ 0 < q.j) ∧
      Bellman q cap ∧ (∑ i ∈ z, cost i) + cap ≤ factorCap := by
    rcases shapeSum_valid_or_empty ha z with hempty | hr
    · have hr0 : r = zeroShape := by simp [r, hempty, shapeSum_empty]
      refine ⟨zeroShape, factorCap, ?_, Or.inl rfl, empty_bellman h2 h3, ?_⟩
      · rw [hr0]
        exact ⟨le_rfl, le_rfl, le_rfl⟩
      · simp [hempty]
    · have hmass := mass_le hlayers (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
        (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
      have hneed : K1_13_8.need ≤ P0_9.layerNeed := by decide
      have hret : RetainedBox r := K1_13_8.retained_bound symbol_count hr
        (by simpa [layerTerm, shapeSum_empty, zeroShape] using hneed.trans hmass)
      have hcost := retained_cost h1 ha hret hfat
      have htr : 1 ≤ r.t := hr.1
      have hjr : 3 * r.t ≤ r.j := hr.2.1
      have hbr : r.j ≤ 3 * r.b := hr.2.2
      have hrj : r.j ≤ 6 := hret.2.1
      have ht : r.t = 1 ∨ r.t = 2 := by omega
      rcases ht with ht | ht
      · refine ⟨oneStart, factorCap - oneReserve, ?_, Or.inr (by decide), one_bellman h4 h5, ?_⟩
        · change 1 ≤ r.b ∧ 3 ≤ r.j ∧ 1 ≤ r.t
          omega
        · change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then _ else _) * r.t at hcost
          rw [ite_eq_left ht, ht, Nat.mul_one] at hcost
          exact (Nat.add_le_add_right hcost _).trans (by decide)
      · refine ⟨twoStart, factorCap - twoReserve, ?_, Or.inr (by decide), two_bellman h6 h7, ?_⟩
        · change 2 ≤ r.b ∧ 6 ≤ r.j ∧ 2 ≤ r.t
          omega
        · change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then _ else _) * r.t at hcost
          rw [ite_eq_right (by omega : r.t ≠ 1), ht] at hcost
          have hreserve : (∑ i ∈ z, cost i) ≤ twoReserve := hcost.trans (by decide)
          exact (Nat.add_le_add_right hreserve _).trans (by decide)
  obtain ⟨q, cap, hqr, hq, ⟨B, order, hB0, horder, hB⟩, haccount⟩ := account
  have hall : InBox (shapeSum a Finset.univ) fullCap := hfits.2
  have hcap {s : Finset (Fin n)} (hs : s ⊆ pos) : InBox (q.plus (shapeSum a s)) fullCap := by
    have hb := shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (shapeSum a s)) (r.plus (shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _,
        Nat.add_le_add_right hqr.2.2 _⟩
    exact inBox_trans hle (inBox_trans hb hall)
  have positive_bound (s : Finset (Fin n)) : s ⊆ pos →
      (∑ i ∈ s, cost i) + B (shapeSum a s) ≤ B zeroShape := by
    refine Finset.strongInductionOn s fun s ih hs => ?_
    by_cases he : s.Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s l he
      let t := s.erase i
      have hti : i ∉ t := Finset.notMem_erase i s
      have hin : insert i t = s := Finset.insert_erase hi
      have hts : t ⊆ s := Finset.erase_subset i s
      have hprev := ih t (Finset.erase_ssubset hi) (hts.trans hs)
      have hvalid : shapeSum a t = zeroShape ∨ Valid (shapeSum a t) := by
        rcases shapeSum_valid_or_empty ha t with ht | ht
        · exact Or.inl (ht ▸ shapeSum_empty a)
        · exact Or.inr ht
      have hsvalid : Valid (shapeSum a s) := by
        rcases shapeSum_valid_or_empty ha s with hempty | hv
        · exact (he.ne_empty hempty).elim
        · exact hv
      have hL : 0 < l i := hpos i (hs hi)
      have hj : 0 < q.j + (shapeSum a s).j := by
        obtain ⟨ht, hidx, _⟩ := hsvalid
        omega
      have hmass : P0_9.layerNeed ≤ availableMass q (shapeSum a s) (l i) :=
        (mass_le hlayers hz hmax (hdisj hs) hqr).trans (K1_13_8.layerSum_le_available symbol_count hq hj)
      have hc := hcap hs
      obtain ⟨horderPos, horderTest⟩ := horder _ hsvalid hc
      have hord : order (shapeSum a s) ≤ l i := by
        rcases horderTest with heq | htest
        · omega
        · by_contra! h
          have hmono : availableMass q (shapeSum a s) (l i) ≤
              availableMass q (shapeSum a s) (order (shapeSum a s) - 1) :=
            K1_13_8.availableMass_mono symbol_count hq hj (by omega)
          exact (not_lt_of_ge (hmass.trans hmono)) htest
      have hstep : edgePrice (a i) (l i) + B (shapeSum a s) ≤ B (shapeSum a t) := by
        have hshape : shapeSum a s = (shapeSum a t).plus (a i) :=
          hin ▸ shapeSum_insert a hti
        refine (Nat.add_le_add_right (edgePrice_anti _ horderPos hord) _).trans ?_
        rw [hshape] at hc ⊢
        exact hB _ _ hvalid (ha i) hc
      have hfee : cost i ≤ edgePrice (a i) (l i) := by
        unfold edgePrice
        split
        · exact le_min (hphys i hL) (hfat i ‹FatEligible (a i)›)
        · exact hphys i hL
      rw [← hin, Finset.sum_insert hti, hin]
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp he, shapeSum_empty]
  have hpaid := positive_bound pos (Finset.Subset.rfl)
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap
  omega

end P0_9_8
end PackSource_P0_9_8Split

section PackSource_P0_9_8_1Aux1
set_option autoImplicit true
namespace P0_9_8_1

open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open P0_9_7 (fatChart divisorBox fat_price_sum hypersurfacePrice singularPrice highCurvePrice)

def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩

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
  · refine ⟨?_, by simp only [P0_9.linearChart, hp.2.1],
      by simp only [P0_9.linearChart, hp.2.1]⟩
    dsimp only [P0_9.linearChart]
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

/-- Within a fixed index and top degree, only total-degree coordinates grow. -/
theorem fatPrice_widen {x y : Shape} (h : TotalLE x y) (hv : IndexFits x) :
    P0_9.fatPrice x ≤ P0_9.fatPrice y := by
  let q : Shape := ⟨952630000, 322000000, 0⟩
  have hp := chamber_widen h
  have hh := fatChart_widen h
  have hc := cut_widen hh
  have hp' : IndexFits x.chamber := hv
  have hh' := fatChart_index x
  have hc' := cut_index hh'
  have hbig : IndexFits divisorBox := Nat.zero_le _
  have hq : IndexFits q := Nat.zero_le _
  rw [fat_price_sum x, fat_price_sum y]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) le_rfl
  · have hd₁ := mixed_mono_total hp (TotalLE.refl divisorBox) hc hh hp' hbig hc' hh'
    have hd₂ := mixed_mono_total hp (TotalLE.refl divisorBox) hc hp hp' hbig hc' hp'
    dsimp only [hypersurfacePrice]
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_) le_rfl
    · exact ceil_mono (Nat.mul_le_mul_left _ hd₁)
    · exact ceil_mono hd₂
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1)
        (by simpa only [pow_two] using Nat.mul_le_mul hh.1 hh.1)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1) hh.1
  · have hs := mixed_mono_total hp hp hh hh hp' hp' hh' hh'
    dsimp only [singularPrice]
    rw [← h.2.2]
    split
    · exact Nat.add_le_add (Nat.add_le_add (ceil_mono (Nat.mul_le_mul_left _ hs))
        (Nat.mul_le_mul_left _ (by simpa only [pow_two] using Nat.mul_le_mul h.1 h.1))) le_rfl
    · exact le_rfl
  · have hcurve := mixed_mono_total hp (TotalLE.refl q) (TotalLE.refl q) hh hp' hq hq hh'
    have hpoint := mixed_mono_total hp (TotalLE.refl q) (TotalLE.refl q) hp hp' hq hq hp'
    exact ceil_mono (Nat.add_le_add (Nat.mul_le_mul_left _ hcurve) (Nat.mul_le_mul_left _ hpoint))

end P0_9_8_1
end PackSource_P0_9_8_1Aux1

section PackSource_P0_9_8_1Proof
set_option autoImplicit true
namespace P0_9_8_1

open K1_13 (Shape ceilDiv mixed32)
open K1_13_8 (Valid RetainedBox)
open P0_9_7 (fatChart divisorBox divisorBox_eq fat_price_sum
  hypersurfacePrice singularPrice highCurvePrice)

-- For the arithmetic checks, encode a chamber shape by its excess total
-- degree, slack index, and top degree.
private def fromSlack (p : Shape) : Shape :=
  ⟨p.b + p.j + 3 * p.t, p.j + 3 * p.t, p.t⟩

private def degreeCoeff (p q r : Shape) : ℕ :=
  16 * (p.j * q.j * r.t + p.j * q.t * r.j + p.t * q.j * r.j) +
  48 * (p.j * q.t * r.t + p.t * q.j * r.t + p.t * q.t * r.j) +
  144 * p.t * q.t * r.t

private def degreePart (p q r s : Shape) : ℕ :=
  p.b * degreeCoeff q r s + q.b * degreeCoeff p r s +
  r.b * degreeCoeff p q s + s.b * degreeCoeff p q r

private def indexPart (p q r s : Shape) : ℕ :=
  24 * (p.j * q.j * r.j * s.t + p.j * q.j * r.t * s.j +
    p.j * q.t * r.j * s.j + p.t * q.j * r.j * s.j) +
  104 * (p.j * q.j * r.t * s.t + (p.j * q.t + p.t * q.j) * (r.j * s.t + r.t * s.j) +
    p.t * q.t * r.j * s.j) +
  312 * ((p.j * q.t + p.t * q.j) * r.t * s.t + p.t * q.t * (r.j * s.t + r.t * s.j)) +
  936 * p.t * q.t * r.t * s.t

-- Polarize once on symbolic coordinates. Each concrete row then checks
-- two natural-number parts rather than reducing sixteen signed volumes.
set_option maxHeartbeats 2000000 in
private theorem mixed_from_parts (p q r s : Shape) (d i : ℕ)
    (hd : degreePart p q r s = d) (hi : indexPart p q r s = i) :
    mixed32 (fromSlack p) (fromSlack q) (fromSlack r) (fromSlack s) = d + i := by
  have h :
      K1_13.difference (K1_13.difference (K1_13.difference
        (K1_13.difference K1_13.volume32 (fromSlack p)) (fromSlack q)) (fromSlack r))
        (fromSlack s) ⟨0, 0, 0⟩ = (↑(degreePart p q r s + indexPart p q r s) : ℤ) := by
    simp only [K1_13.difference, K1_13.volume32, Shape.plus, fromSlack,
      degreePart, degreeCoeff, indexPart, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, Nat.cast_ofNat]
    ring
  unfold mixed32
  rw [h, Int.toNat_natCast, hd, hi]

private abbrev divisorSlack : Shape := ⟨22901, 12106, 0⟩
private abbrev resultantSlack : Shape := ⟨630630000, 322000000, 0⟩
private abbrev resultantBox : Shape := ⟨952630000, 322000000, 0⟩

private theorem linear_chart_value {x h : Shape} (hx : x.chamber = x) (ht : x.t = 1)
    (hj : 3 + 133552 * (x.j - 2) = h.j)
    (hb : max (1 + 133552 * (x.b - 1)) h.j = h.b)
    (hh : min 133553 (h.j / 3) = h.t) : fatChart x = h := by
  rw [fatChart, ite_eq_left ht, hx]
  change (⟨max (1 + 133552 * (x.b - 1)) (3 + 133552 * (x.j - 2)),
    3 + 133552 * (x.j - 2), min 133553 ((3 + 133552 * (x.j - 2)) / 3)⟩ : Shape) = h
  rw [hj, hb, hh]

private theorem general_chart_value {x h : Shape} (hx : x.chamber = x) (ht : x.t ≠ 1)
    (hj : 2 * 133556 * (x.j - 3) + 133556 + 3 = h.j)
    (hb : max (1 + 2 * 133556 * (x.b - 1)) h.j = h.b)
    (hh : min (2 * 133556 * (x.t - 1) + 133556 + 1) (h.j / 3) = h.t) :
    fatChart x = h := by
  rw [fatChart, ite_eq_right ht, hx]
  change (⟨max (1 + 2 * 133556 * (x.b - 1)) (2 * 133556 * (x.j - 3) + 133556 + 3),
    2 * 133556 * (x.j - 3) + 133556 + 3,
    min (2 * 133556 * (x.t - 1) + 133556 + 1) ((2 * 133556 * (x.j - 3) + 133556 + 3) / 3)⟩ :
      Shape) = h
  rw [hj, hb, hh]

private theorem chart_covers_cut (h : Shape) (hb : 35007 ≤ h.b) (hj : 12107 ≤ h.j)
    (hjb : h.j ≤ h.b) (ht : 1 ≤ h.t) : divisorCut h = h := by
  rw [divisorCut, divisorBox_eq]
  change (⟨max (max h.b 35007) (max h.j 12107), max h.j 12107, max 1 h.t⟩ : Shape) = h
  rw [max_eq_left hb, max_eq_left hj, max_eq_left hjb, max_eq_right ht]

private theorem isolated_value : K1_13_7.isolatedPrice = 344924340099310 := by
  change ceilDiv (3 * 322000000 ^ 2 * (2 * 952630000 - 322000000))
    (4 * 41481 * (41481 - 33184 + 1) * 1037) = 344924340099310
  decide

private theorem singular_from_mix {x h : Shape} {m fee : ℕ}
    (hx : x.chamber = x) (hh : fatChart x = h) (ht : 1 < x.t)
    (hm : mixed32 x x h h = m)
    (hfee : ceilDiv (4 * x.t * m) 32 + x.t * x.b ^ 2 + 1 = fee) :
    singularPrice x = fee := by
  dsimp only [singularPrice]
  rw [ite_eq_left ht, hx, hh, hm]
  exact hfee

-- At all five widened rows the chart already contains the divisor cut box.
private theorem fee_of_parts {x h : Shape} {md mp mc mq divs singular curves cap : ℕ}
    (hx : x.chamber = x) (hh : fatChart x = h) (hc : divisorCut h = h)
    (hd : mixed32 x ⟨35007, 12106, 0⟩ h h = md)
    (hp : mixed32 x ⟨35007, 12106, 0⟩ h x = mp)
    (hcurve : mixed32 x resultantBox resultantBox h = mc)
    (hpoint : mixed32 x resultantBox resultantBox x = mq)
    (hdivs : ceilDiv (81936 * md) 1493024 + ceilDiv mp 32 +
      20 * x.b * h.b ^ 2 + 5 * 133551 * x.b * h.b + 1 = divs)
    (hsingular : singularPrice x = singular)
    (hcurves : ceilDiv (81936 * mc + 46657 * mq) 438518452948160 = curves)
    (hcap : divs + singular + curves + 344924340099310 ≤ cap) :
    P0_9.fatPrice x ≤ cap := by
  have hdFee : hypersurfacePrice x = divs := by
    dsimp only [hypersurfacePrice]
    rw [hh, hx]
    change ceilDiv (P0.t * mixed32 x divisorBox (divisorCut h) h) (32 * P0_9.incidenceGap) +
      ceilDiv (mixed32 x divisorBox (divisorCut h) x) 32 +
      20 * x.b * h.b ^ 2 + 5 * P0_9.physicalDegree * x.b * h.b + 1 = divs
    rw [hc, divisorBox_eq, hd, hp]
    exact hdivs
  have hcFee : highCurvePrice x = curves := by
    dsimp only [highCurvePrice]
    rw [hh, hx, hcurve, hpoint]
    exact hcurves
  rw [fat_price_sum, hdFee, hsingular, hcFee, isolated_value]
  exact hcap

private theorem row_19_3_1 : P0_9.fatPrice ⟨19, 3, 1⟩ ≤ 37000000000000000 := by
  let p : Shape := ⟨16, 0, 1⟩
  let h : Shape := ⟨2270382, 1, 44518⟩
  refine fee_of_parts (h := fromSlack h) (divs := 10453681234025154)
    (singular := 0) (curves := 1176394129606956) rfl
    (linear_chart_value rfl rfl (by decide) (by decide) (by decide))
    (chart_covers_cut _ (by decide) (by decide) (by decide) (by decide))
    (mixed_from_parts p divisorSlack h h 142427443570147408 7485711019866736 (by decide) (by decide))
    (mixed_from_parts p divisorSlack h p 2293912019216 168148950320 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack h 5815924429033600000000000
      480046136864000000000000 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack p 72580242560000000000
      10783136000000000000 (by decide) (by decide)) ?_ rfl ?_ ?_ <;> decide

private theorem row_17_4_1 : P0_9.fatPrice ⟨17, 4, 1⟩ ≤ 37000000000000000 := by
  let p : Shape := ⟨13, 1, 1⟩
  let h : Shape := ⟨1869726, 2, 89035⟩
  refine fee_of_parts (h := fromSlack h) (divs := 23123728418733519)
    (singular := 0) (curves := 1591533419904956) rfl
    (linear_chart_value rfl rfl (by decide) (by decide) (by decide))
    (chart_covers_cut _ (by decide) (by decide) (by decide) (by decide))
    (mixed_from_parts p divisorSlack h h 352700504707863008 39922849327607296 (by decide) (by decide))
    (mixed_from_parts p divisorSlack h p 4126342779232 586358274464 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack h 7336138575619840000000000
      1181637609152000000000000 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack p 75622601600000000000
      15759968000000000000 (by decide) (by decide)) ?_ rfl ?_ ?_ <;> decide

private theorem row_13_5_1 : P0_9.fatPrice ⟨13, 5, 1⟩ ≤ 37000000000000000 := by
  let p : Shape := ⟨8, 2, 1⟩
  let h : Shape := ⟨1201966, 0, 133553⟩
  refine fee_of_parts (h := fromSlack h) (divs := 33837966342768932)
    (singular := 0) (curves := 1907793097251138) rfl
    (linear_chart_value rfl rfl (by decide) (by decide) (by decide))
    (chart_covers_cut _ (by decide) (by decide) (by decide) (by decide))
    (mixed_from_parts p divisorSlack h h 491882078745609776 112282302346112080 (by decide) (by decide))
    (mixed_from_parts p divisorSlack h p 4922605496592 1332237117232 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack h 8105594530812800000000000
      2104791006304000000000000 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack p 72029184640000000000
      20736800000000000000 (by decide) (by decide)) ?_ rfl ?_ ?_ <;> decide

private theorem row_6_6_1 : P0_9.fatPrice ⟨6, 6, 1⟩ ≤ 37000000000000000 := by
  let p : Shape := ⟨0, 3, 1⟩
  let h : Shape := ⟨133550, 133552, 133553⟩
  refine fee_of_parts (h := fromSlack h) (divs := 25679147416072872)
    (singular := 0) (curves := 1693930815024820) rfl
    (linear_chart_value rfl rfl (by decide) (by decide) (by decide))
    (chart_covers_cut _ (by decide) (by decide) (by decide) (by decide))
    (mixed_from_parts p divisorSlack h h 250967793567208608 215926857794997344 (by decide) (by decide))
    (mixed_from_parts p divisorSlack h p 2434927631616 2263506662912 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack h 6296348000902400000000000
      2769459361984000000000000 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack p 58482103680000000000
      25713632000000000000 (by decide) (by decide)) ?_ rfl ?_ ?_ <;> decide

private theorem row_6_6_2 : P0_9.fatPrice ⟨6, 6, 2⟩ ≤ 97000000000000000 := by
  let p : Shape := ⟨0, 0, 2⟩
  let h : Shape := ⟨400666, 2, 311631⟩
  have hh : fatChart ⟨6, 6, 2⟩ = fromSlack h :=
    general_chart_value rfl (by decide) (by decide) (by decide) (by decide)
  have hs : singularPrice ⟨6, 6, 2⟩ = 126858722193393 :=
    singular_from_mix rfl hh (by decide)
      (mixed_from_parts p p h h 143838965786880 363595922986400 (by decide) (by decide)) (by decide)
  refine fee_of_parts (h := fromSlack h) (divs := 91557975241521715)
    (curves := 3774330861475639) rfl hh
    (chart_covers_cut _ (by decide) (by decide) (by decide) (by decide))
    (mixed_from_parts p divisorSlack h h 930735258352267680 733615373944526688 (by decide) (by decide))
    (mixed_from_parts p divisorSlack h p 5042014654272 4708220969920 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack h 13479281873388800000000000
      6720728863296000000000000 (by decide) (by decide))
    (mixed_from_parts p resultantSlack resultantSlack p 77976138240000000000
      43132544000000000000 (by decide) (by decide)) ?_ hs ?_ ?_ <;> decide

private theorem shape_cases {j t : ℕ} (ht : 1 ≤ t) (hjt : 3 * t ≤ j) (hj : j ≤ 6) :
    (j = 3 ∧ t = 1) ∨ (j = 4 ∧ t = 1) ∨ (j = 5 ∧ t = 1) ∨
      (j = 6 ∧ t = 1) ∨ (j = 6 ∧ t = 2) := by omega

theorem proof : P0_9_8.c1 := by
  intro ⟨b, j, t⟩ ha hb
  have hjt : 3 * t ≤ j := ha.2.1
  change P0_9.fatPrice ⟨b, j, t⟩ ≤ (if t = 1 then P0_9_8.oneReserve else 48500000000000000) * t
  rcases shape_cases ha.1 hjt hb.2.1 with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first | rw [ite_eq_left (rfl : 1 = 1), Nat.mul_one] | rw [ite_eq_right (by decide : (2 : ℕ) ≠ 1)]
  · exact (fatPrice_widen (y := ⟨19, 3, 1⟩) ⟨hb.1, rfl, rfl⟩ hjt).trans row_19_3_1
  · exact (fatPrice_widen (y := ⟨17, 4, 1⟩) ⟨hb.2.2.1 le_rfl, rfl, rfl⟩ hjt).trans row_17_4_1
  · exact (fatPrice_widen (y := ⟨13, 5, 1⟩) ⟨hb.2.2.2.1 le_rfl, rfl, rfl⟩ hjt).trans row_13_5_1
  · exact (fatPrice_widen (y := ⟨6, 6, 1⟩) ⟨hb.2.2.2.2 le_rfl, rfl, rfl⟩ hjt).trans row_6_6_1
  · exact (fatPrice_widen (y := ⟨6, 6, 2⟩) ⟨hb.2.2.2.2 le_rfl, rfl, rfl⟩ hjt).trans row_6_6_2

end P0_9_8_1
end PackSource_P0_9_8_1Proof

section PackSource_P0_9_8_2Proof
set_option autoImplicit true
namespace P0_9_8_2

open K1_13_8 (zeroShape availableMass zeroMass fastRemaining)
open K1_13_8_2 (Threshold)
open scoped BigOperators

-- The recursive sum and its bridge to the finite sum come from the light
-- K1_13_8_2Order proof. Here each endpoint uses exact counts in short blocks.
private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n

private theorem sumBelow_eq (f : ℕ → ℕ) (n : ℕ) :
    sumBelow f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Finset.sum_range_succ, ih]

private theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]

private def tailTerm (b j k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * b) ((k + 1) * j)

private theorem extend {f : ℕ → ℕ} {m n N x y total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = y)
    (hlen : m + n = N) (hvalue : x + y = total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, hvalue]

private theorem zeroMass_eq (b j : ℕ) :
    zeroMass b j = sumBelow (tailTerm b j) (1650 / j) :=
  (sumBelow_eq _ _).symm

private theorem startCount : fastRemaining 0 0 = 408959263788 := rfl

private theorem tail107_46 : zeroMass 107 46 = 2777310481924 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 107 46) 8 = 1990089055321 := rfl
  have h16 : sumBelow (tailTerm 107 46) 16 = 2632171312116 :=
    extend h8 (n := 8) (y := 642082256795) rfl rfl rfl
  have h24 : sumBelow (tailTerm 107 46) 24 = 2766297614992 :=
    extend h16 (n := 8) (y := 134126302876) rfl rfl rfl
  have h32 : sumBelow (tailTerm 107 46) 32 = 2777274119457 :=
    extend h24 (n := 8) (y := 10976504465) rfl rfl rfl
  exact extend h32 (n := 3) (y := 36362467) rfl rfl rfl

private theorem tail14_41 : zeroMass 14 41 = 3970190048331 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 14 41) 8 = 2336190024682 := rfl
  have h16 : sumBelow (tailTerm 14 41) 16 = 3452340000437 :=
    extend h8 (n := 8) (y := 1116149975755) rfl rfl rfl
  have h24 : sumBelow (tailTerm 14 41) 24 = 3868549656470 :=
    extend h16 (n := 8) (y := 416209656033) rfl rfl rfl
  have h32 : sumBelow (tailTerm 14 41) 32 = 3964090215208 :=
    extend h24 (n := 8) (y := 95540558738) rfl rfl rfl
  exact extend h32 (n := 8) (y := 6099833123) rfl rfl rfl

private theorem tail61_31 : zeroMass 61 31 = 4415402865060 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 61 31) 8 = 2376289374114 := rfl
  have h16 : sumBelow (tailTerm 61 31) 16 = 3600530804726 :=
    extend h8 (n := 8) (y := 1224241430612) rfl rfl rfl
  have h24 : sumBelow (tailTerm 61 31) 24 = 4152276962484 :=
    extend h16 (n := 8) (y := 551746157758) rfl rfl rfl
  have h32 : sumBelow (tailTerm 61 31) 32 = 4355381692678 :=
    extend h24 (n := 8) (y := 203104730194) rfl rfl rfl
  have h40 : sumBelow (tailTerm 61 31) 40 = 4408451768458 :=
    extend h32 (n := 8) (y := 53070075780) rfl rfl rfl
  have h48 : sumBelow (tailTerm 61 31) 48 = 4415298639608 :=
    extend h40 (n := 8) (y := 6846871150) rfl rfl rfl
  exact extend h48 (n := 5) (y := 104225452) rfl rfl rfl

private theorem tail11_13 : zeroMass 11 13 = 12288354800456 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 11 13) 8 = 2919741031928 := rfl
  have h16 : sumBelow (tailTerm 11 13) 16 = 5275426778002 :=
    extend h8 (n := 8) (y := 2355685746074) rfl rfl rfl
  have h24 : sumBelow (tailTerm 11 13) 24 = 7148190755122 :=
    extend h16 (n := 8) (y := 1872763977120) rfl rfl rfl
  have h32 : sumBelow (tailTerm 11 13) 32 = 8611895838922 :=
    extend h24 (n := 8) (y := 1463705083800) rfl rfl rfl
  have h40 : sumBelow (tailTerm 11 13) 40 = 9733376237796 :=
    extend h32 (n := 8) (y := 1121480398874) rfl rfl rfl
  have h48 : sumBelow (tailTerm 11 13) 48 = 10572679460324 :=
    extend h40 (n := 8) (y := 839303222528) rfl rfl rfl
  have h56 : sumBelow (tailTerm 11 13) 56 = 11183308286108 :=
    extend h48 (n := 8) (y := 610628825784) rfl rfl rfl
  have h64 : sumBelow (tailTerm 11 13) 64 = 11612462739638 :=
    extend h56 (n := 8) (y := 429154453530) rfl rfl rfl
  have h72 : sumBelow (tailTerm 11 13) 72 = 11901282057878 :=
    extend h64 (n := 8) (y := 288819318240) rfl rfl rfl
  have h80 : sumBelow (tailTerm 11 13) 80 = 12085086661102 :=
    extend h72 (n := 8) (y := 183804603224) rfl rfl rfl
  have h88 : sumBelow (tailTerm 11 13) 88 = 12193620126600 :=
    extend h80 (n := 8) (y := 108533465498) rfl rfl rfl
  have h96 : sumBelow (tailTerm 11 13) 96 = 12251291156424 :=
    extend h88 (n := 8) (y := 57671029824) rfl rfl rfl
  have h104 : sumBelow (tailTerm 11 13) 104 = 12277415548224 :=
    extend h96 (n := 8) (y := 26124391800) rfl rfl rfl
  have h112 : sumBelow (tailTerm 11 13) 112 = 12286458168794 :=
    extend h104 (n := 8) (y := 9042620570) rfl rfl rfl
  have h120 : sumBelow (tailTerm 11 13) 120 = 12288274921978 :=
    extend h112 (n := 8) (y := 1816753184) rfl rfl rfl
  exact extend h120 (n := 6) (y := 79878478) rfl rfl rfl

private theorem tail9_7 : zeroMass 9 7 = 21917430255644 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 9 7) 8 = 3064789617706 := rfl
  have h16 : sumBelow (tailTerm 9 7) 16 = 5783491051046 :=
    extend h8 (n := 8) (y := 2718701433340) rfl rfl rfl
  have h24 : sumBelow (tailTerm 9 7) 24 = 8185444121240 :=
    extend h16 (n := 8) (y := 2401953070194) rfl rfl rfl
  have h32 : sumBelow (tailTerm 9 7) 32 = 10298354572210 :=
    extend h24 (n := 8) (y := 2112910450970) rfl rfl rfl
  have h40 : sumBelow (tailTerm 9 7) 40 = 12148337470526 :=
    extend h32 (n := 8) (y := 1849982898316) rfl rfl rfl
  have h48 : sumBelow (tailTerm 9 7) 48 = 13759960598752 :=
    extend h40 (n := 8) (y := 1611623128226) rfl rfl rfl
  have h56 : sumBelow (tailTerm 9 7) 56 = 15156287852202 :=
    extend h48 (n := 8) (y := 1396327253450) rfl rfl rfl
  have h64 : sumBelow (tailTerm 9 7) 64 = 16358922638726 :=
    extend h56 (n := 8) (y := 1202634786524) rfl rfl rfl
  have h72 : sumBelow (tailTerm 9 7) 72 = 17388051272216 :=
    extend h64 (n := 8) (y := 1029128633490) rfl rfl rfl
  have h80 : sumBelow (tailTerm 9 7) 80 = 18262486369362 :=
    extend h72 (n := 8) (y := 874435097146) rfl rfl rfl
  have h88 : sumBelow (tailTerm 9 7) 88 = 18999710249278 :=
    extend h80 (n := 8) (y := 737223879916) rfl rfl rfl
  have h96 : sumBelow (tailTerm 9 7) 96 = 19615918327168 :=
    extend h88 (n := 8) (y := 616208077890) rfl rfl rfl
  have h104 : sumBelow (tailTerm 9 7) 104 = 20126062511082 :=
    extend h96 (n := 8) (y := 510144183914) rfl rfl rfl
  have h112 : sumBelow (tailTerm 9 7) 112 = 20543894601382 :=
    extend h104 (n := 8) (y := 417832090300) rfl rfl rfl
  have h120 : sumBelow (tailTerm 9 7) 120 = 20882009684568 :=
    extend h112 (n := 8) (y := 338115083186) rfl rfl rfl
  have h128 : sumBelow (tailTerm 9 7) 128 = 21151889530034 :=
    extend h120 (n := 8) (y := 269879845466) rfl rfl rfl
  have h136 : sumBelow (tailTerm 9 7) 136 = 21363945989374 :=
    extend h128 (n := 8) (y := 212056459340) rfl rfl rfl
  have h144 : sumBelow (tailTerm 9 7) 144 = 21527564390368 :=
    extend h136 (n := 8) (y := 163618400994) rfl rfl rfl
  have h152 : sumBelow (tailTerm 9 7) 152 = 21651146933738 :=
    extend h144 (n := 8) (y := 123582543370) rfl rfl rfl
  have h160 : sumBelow (tailTerm 9 7) 160 = 21742156092294 :=
    extend h152 (n := 8) (y := 91009158556) rfl rfl rfl
  have h168 : sumBelow (tailTerm 9 7) 168 = 21807158005080 :=
    extend h160 (n := 8) (y := 65001912786) rfl rfl rfl
  have h176 : sumBelow (tailTerm 9 7) 176 = 21851865874130 :=
    extend h168 (n := 8) (y := 44707869050) rfl rfl rfl
  have h184 : sumBelow (tailTerm 9 7) 184 = 21881183363454 :=
    extend h176 (n := 8) (y := 29317489324) rfl rfl rfl
  have h192 : sumBelow (tailTerm 9 7) 192 = 21899247993344 :=
    extend h184 (n := 8) (y := 18064629890) rfl rfl rfl
  have h200 : sumBelow (tailTerm 9 7) 200 = 21909474537130 :=
    extend h192 (n := 8) (y := 10226543786) rfl rfl rfl
  have h208 : sumBelow (tailTerm 9 7) 208 = 21914598420006 :=
    extend h200 (n := 8) (y := 5123882876) rfl rfl rfl
  have h216 : sumBelow (tailTerm 9 7) 216 = 21916719113496 :=
    extend h208 (n := 8) (y := 2120693490) rfl rfl rfl
  have h224 : sumBelow (tailTerm 9 7) 224 = 21917343532210 :=
    extend h216 (n := 8) (y := 624418714) rfl rfl rfl
  have h232 : sumBelow (tailTerm 9 7) 232 = 21917429432510 :=
    extend h224 (n := 8) (y := 85900300) rfl rfl rfl
  exact extend h232 (n := 3) (y := 823134) rfl rfl rfl

private theorem tail22_4 : zeroMass 22 4 = 22258909366749 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 22 4) 8 = 3078808089988 := rfl
  have h16 : sumBelow (tailTerm 22 4) 16 = 5832606048938 :=
    extend h8 (n := 8) (y := 2753797958950) rfl rfl rfl
  have h24 : sumBelow (tailTerm 22 4) 24 = 8285674381416 :=
    extend h16 (n := 8) (y := 2453068332478) rfl rfl rfl
  have h32 : sumBelow (tailTerm 22 4) 32 = 10461116790236 :=
    extend h24 (n := 8) (y := 2175442408820) rfl rfl rfl
  have h40 : sumBelow (tailTerm 22 4) 40 = 12380888374402 :=
    extend h32 (n := 8) (y := 1919771584166) rfl rfl rfl
  have h48 : sumBelow (tailTerm 22 4) 48 = 14065823821136 :=
    extend h40 (n := 8) (y := 1684935446734) rfl rfl rfl
  have h56 : sumBelow (tailTerm 22 4) 56 = 15535665601204 :=
    extend h48 (n := 8) (y := 1469841780068) rfl rfl rfl
  have h64 : sumBelow (tailTerm 22 4) 64 = 16809092166362 :=
    extend h56 (n := 8) (y := 1273426565158) rfl rfl rfl
  have h72 : sumBelow (tailTerm 22 4) 72 = 17903746141880 :=
    extend h64 (n := 8) (y := 1094653975518) rfl rfl rfl
  have h80 : sumBelow (tailTerm 22 4) 80 = 18836262521868 :=
    extend h72 (n := 8) (y := 932516379988) rfl rfl rfl
  have h88 : sumBelow (tailTerm 22 4) 88 = 19622296866226 :=
    extend h80 (n := 8) (y := 786034344358) rfl rfl rfl
  have h96 : sumBelow (tailTerm 22 4) 96 = 20276553493664 :=
    extend h88 (n := 8) (y := 654256627438) rfl rfl rfl
  have h104 : sumBelow (tailTerm 22 4) 104 = 20812813677028 :=
    extend h96 (n := 8) (y := 536260183364) rfl rfl rfl
  have h112 : sumBelow (tailTerm 22 4) 112 = 21243963839754 :=
    extend h104 (n := 8) (y := 431150162726) rfl rfl rfl
  have h120 : sumBelow (tailTerm 22 4) 120 = 21582023749384 :=
    extend h112 (n := 8) (y := 338059909630) rfl rfl rfl
  have h128 : sumBelow (tailTerm 22 4) 128 = 21838174712892 :=
    extend h120 (n := 8) (y := 256150963508) rfl rfl rfl
  have h136 : sumBelow (tailTerm 22 4) 136 = 22022789603760 :=
    extend h128 (n := 8) (y := 184614890868) rfl rfl rfl
  have h144 : sumBelow (tailTerm 22 4) 144 = 22145635335938 :=
    extend h136 (n := 8) (y := 122845732178) rfl rfl rfl
  have h152 : sumBelow (tailTerm 22 4) 152 = 22216931303018 :=
    extend h144 (n := 8) (y := 71295967080) rfl rfl rfl
  have h160 : sumBelow (tailTerm 22 4) 160 = 22249037811790 :=
    extend h152 (n := 8) (y := 32106508772) rfl rfl rfl
  have h168 : sumBelow (tailTerm 22 4) 168 = 22257872440936 :=
    extend h160 (n := 8) (y := 8834629146) rfl rfl rfl
  have h176 : sumBelow (tailTerm 22 4) 176 = 22258894821548 :=
    extend h168 (n := 8) (y := 1022380612) rfl rfl rfl
  have h184 : sumBelow (tailTerm 22 4) 184 = 22258909366749 :=
    extend h176 (n := 8) (y := 14545201) rfl rfl rfl
  have h192 : sumBelow (tailTerm 22 4) 192 = 22258909366749 :=
    extend h184 (n := 8) (y := 0) rfl rfl rfl
  have h200 : sumBelow (tailTerm 22 4) 200 = 22258909366749 :=
    extend h192 (n := 8) (y := 0) rfl rfl rfl
  have h208 : sumBelow (tailTerm 22 4) 208 = 22258909366749 :=
    extend h200 (n := 8) (y := 0) rfl rfl rfl
  have h216 : sumBelow (tailTerm 22 4) 216 = 22258909366749 :=
    extend h208 (n := 8) (y := 0) rfl rfl rfl
  have h224 : sumBelow (tailTerm 22 4) 224 = 22258909366749 :=
    extend h216 (n := 8) (y := 0) rfl rfl rfl
  have h232 : sumBelow (tailTerm 22 4) 232 = 22258909366749 :=
    extend h224 (n := 8) (y := 0) rfl rfl rfl
  have h240 : sumBelow (tailTerm 22 4) 240 = 22258909366749 :=
    extend h232 (n := 8) (y := 0) rfl rfl rfl
  have h248 : sumBelow (tailTerm 22 4) 248 = 22258909366749 :=
    extend h240 (n := 8) (y := 0) rfl rfl rfl
  have h256 : sumBelow (tailTerm 22 4) 256 = 22258909366749 :=
    extend h248 (n := 8) (y := 0) rfl rfl rfl
  have h264 : sumBelow (tailTerm 22 4) 264 = 22258909366749 :=
    extend h256 (n := 8) (y := 0) rfl rfl rfl
  have h272 : sumBelow (tailTerm 22 4) 272 = 22258909366749 :=
    extend h264 (n := 8) (y := 0) rfl rfl rfl
  have h280 : sumBelow (tailTerm 22 4) 280 = 22258909366749 :=
    extend h272 (n := 8) (y := 0) rfl rfl rfl
  have h288 : sumBelow (tailTerm 22 4) 288 = 22258909366749 :=
    extend h280 (n := 8) (y := 0) rfl rfl rfl
  have h296 : sumBelow (tailTerm 22 4) 296 = 22258909366749 :=
    extend h288 (n := 8) (y := 0) rfl rfl rfl
  have h304 : sumBelow (tailTerm 22 4) 304 = 22258909366749 :=
    extend h296 (n := 8) (y := 0) rfl rfl rfl
  have h312 : sumBelow (tailTerm 22 4) 312 = 22258909366749 :=
    extend h304 (n := 8) (y := 0) rfl rfl rfl
  have h320 : sumBelow (tailTerm 22 4) 320 = 22258909366749 :=
    extend h312 (n := 8) (y := 0) rfl rfl rfl
  have h328 : sumBelow (tailTerm 22 4) 328 = 22258909366749 :=
    extend h320 (n := 8) (y := 0) rfl rfl rfl
  have h336 : sumBelow (tailTerm 22 4) 336 = 22258909366749 :=
    extend h328 (n := 8) (y := 0) rfl rfl rfl
  have h344 : sumBelow (tailTerm 22 4) 344 = 22258909366749 :=
    extend h336 (n := 8) (y := 0) rfl rfl rfl
  have h352 : sumBelow (tailTerm 22 4) 352 = 22258909366749 :=
    extend h344 (n := 8) (y := 0) rfl rfl rfl
  have h360 : sumBelow (tailTerm 22 4) 360 = 22258909366749 :=
    extend h352 (n := 8) (y := 0) rfl rfl rfl
  have h368 : sumBelow (tailTerm 22 4) 368 = 22258909366749 :=
    extend h360 (n := 8) (y := 0) rfl rfl rfl
  have h376 : sumBelow (tailTerm 22 4) 376 = 22258909366749 :=
    extend h368 (n := 8) (y := 0) rfl rfl rfl
  have h384 : sumBelow (tailTerm 22 4) 384 = 22258909366749 :=
    extend h376 (n := 8) (y := 0) rfl rfl rfl
  have h392 : sumBelow (tailTerm 22 4) 392 = 22258909366749 :=
    extend h384 (n := 8) (y := 0) rfl rfl rfl
  have h400 : sumBelow (tailTerm 22 4) 400 = 22258909366749 :=
    extend h392 (n := 8) (y := 0) rfl rfl rfl
  have h408 : sumBelow (tailTerm 22 4) 408 = 22258909366749 :=
    extend h400 (n := 8) (y := 0) rfl rfl rfl
  exact extend h408 (n := 4) (y := 0) rfl rfl rfl

private theorem tail3_7 : zeroMass 3 7 = 24019410897176 := by
  rw [zeroMass_eq]
  have h8 : sumBelow (tailTerm 3 7) 8 = 3090014092996 := rfl
  have h16 : sumBelow (tailTerm 3 7) 16 = 5872381544378 :=
    extend h8 (n := 8) (y := 2782367451382) rfl rfl rfl
  have h24 : sumBelow (tailTerm 3 7) 24 = 8368138443116 :=
    extend h16 (n := 8) (y := 2495756898738) rfl rfl rfl
  have h32 : sumBelow (tailTerm 3 7) 32 = 10597589667760 :=
    extend h24 (n := 8) (y := 2229451224644) rfl rfl rfl
  have h40 : sumBelow (tailTerm 3 7) 40 = 12580307328854 :=
    extend h32 (n := 8) (y := 1982717661094) rfl rfl rfl
  have h48 : sumBelow (tailTerm 3 7) 48 = 14335129204456 :=
    extend h40 (n := 8) (y := 1754821875602) rfl rfl rfl
  have h56 : sumBelow (tailTerm 3 7) 56 = 15880157179116 :=
    extend h48 (n := 8) (y := 1545027974660) rfl rfl rfl
  have h64 : sumBelow (tailTerm 3 7) 64 = 17232755686274 :=
    extend h56 (n := 8) (y := 1352598507158) rfl rfl rfl
  have h72 : sumBelow (tailTerm 3 7) 72 = 18409550143796 :=
    extend h64 (n := 8) (y := 1176794457522) rfl rfl rfl
  have h80 : sumBelow (tailTerm 3 7) 80 = 19426425392952 :=
    extend h72 (n := 8) (y := 1016875249156) rfl rfl rfl
  have h88 : sumBelow (tailTerm 3 7) 88 = 20298524140798 :=
    extend h80 (n := 8) (y := 872098747846) rfl rfl rfl
  have h96 : sumBelow (tailTerm 3 7) 96 = 21040245395728 :=
    extend h88 (n := 8) (y := 741721254930) rfl rfl rfl
  have h104 : sumBelow (tailTerm 3 7) 104 = 21665242906452 :=
    extend h96 (n := 8) (y := 624997510724) rfl rfl rfl
  have h112 : sumBelow (tailTerm 3 7) 112 = 22186423604362 :=
    extend h104 (n := 8) (y := 521180697910) rfl rfl rfl
  have h120 : sumBelow (tailTerm 3 7) 120 = 22615946039100 :=
    extend h112 (n := 8) (y := 429522434738) rfl rfl rfl
  have h128 : sumBelow (tailTerm 3 7) 128 = 22965218817536 :=
    extend h120 (n := 8) (y := 349272778436) rfl rfl rfl
  have h136 : sumBelow (tailTerm 3 7) 136 = 23244899046118 :=
    extend h128 (n := 8) (y := 279680228582) rfl rfl rfl
  have h144 : sumBelow (tailTerm 3 7) 144 = 23464890766456 :=
    extend h136 (n := 8) (y := 219991720338) rfl rfl rfl
  have h152 : sumBelow (tailTerm 3 7) 152 = 23634343394300 :=
    extend h144 (n := 8) (y := 169452627844) rfl rfl rfl
  have h160 : sumBelow (tailTerm 3 7) 160 = 23761650161874 :=
    extend h152 (n := 8) (y := 127306767574) rfl rfl rfl
  have h168 : sumBelow (tailTerm 3 7) 168 = 23854446553476 :=
    extend h160 (n := 8) (y := 92796391602) rfl rfl rfl
  have h176 : sumBelow (tailTerm 3 7) 176 = 23919608744456 :=
    extend h168 (n := 8) (y := 65162190980) rfl rfl rfl
  have h184 : sumBelow (tailTerm 3 7) 184 = 23963252043534 :=
    extend h176 (n := 8) (y := 43643299078) rfl rfl rfl
  have h192 : sumBelow (tailTerm 3 7) 192 = 23990729328416 :=
    extend h184 (n := 8) (y := 27477284882) rfl rfl rfl
  have h200 : sumBelow (tailTerm 3 7) 200 = 24006629484772 :=
    extend h192 (n := 8) (y := 15900156356) rfl rfl rfl
  have h208 : sumBelow (tailTerm 3 7) 208 = 24014775848538 :=
    extend h200 (n := 8) (y := 8146363766) rfl rfl rfl
  have h216 : sumBelow (tailTerm 3 7) 216 = 24018224641548 :=
    extend h208 (n := 8) (y := 3448793010) rfl rfl rfl
  have h224 : sumBelow (tailTerm 3 7) 224 = 24019263410512 :=
    extend h216 (n := 8) (y := 1038768964) rfl rfl rfl
  have h232 : sumBelow (tailTerm 3 7) 232 = 24019409469302 :=
    extend h224 (n := 8) (y := 146058790) rfl rfl rfl
  exact extend h232 (n := 3) (y := 1427874) rfl rfl rfl

private theorem threshold_lt (s : Threshold) {tail : ℕ}
    (htail : zeroMass s.b s.j = tail)
    (h : (s.l - 1) * 408959263788 + tail < P0_9.layerNeed) :
    availableMass zeroShape ⟨s.b, s.j, 0⟩ (s.l - 1) < P0_9.layerNeed := by
  simp only [availableMass, zeroShape, Nat.zero_add, Nat.mul_zero, ite_true]
  change (s.l - 1) * fastRemaining 0 0 + zeroMass s.b s.j < P0_9.layerNeed
  rw [startCount, htail]
  exact h

theorem proof : P0_9_8.c2 := by
  intro s hs
  simp [P0_9_8.emptyThresholds] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact threshold_lt ⟨107, 46, 60⟩ tail107_46 (by decide)
  · exact threshold_lt ⟨14, 41, 57⟩ tail14_41 (by decide)
  · exact threshold_lt ⟨61, 31, 56⟩ tail61_31 (by decide)
  · exact threshold_lt ⟨11, 13, 37⟩ tail11_13 (by decide)
  · exact threshold_lt ⟨9, 7, 13⟩ tail9_7 (by decide)
  · exact threshold_lt ⟨22, 4, 12⟩ tail22_4 (by decide)
  · exact threshold_lt ⟨3, 7, 8⟩ tail3_7 (by decide)

end P0_9_8_2
end PackSource_P0_9_8_2Proof

section PackSource_P0_9_8_3Tariff
set_option autoImplicit true
namespace P0_9_8_3

open K1_13
open K1_13_8_2 (Chamber mixed_mono)

private theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩

private theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩

private theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩

private theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩

private theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩

private theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩

private theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩

private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega

private theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
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
    P0_9.surfaceNumerator32 p q ≤ P0_9.surfaceNumerator32 p' q := by
  let L := P0_9.taylorLength
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

private theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)

/-- Retuned shape monotonicity at a fixed order. -/
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : P0_9.physicalPrice x l ≤ P0_9.physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := P0_9.primaryBox
  let L := P0_9.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, by decide⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (P0.t + 2*P0_9.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P0.t + 2*P0_9.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P0.t hc) (Nat.mul_le_mul_left (2*P0_9.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*P0_9.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)

end P0_9_8_3
end PackSource_P0_9_8_3Tariff

section PackSource_P0_9_8_3Rows
set_option autoImplicit true
namespace P0_9_8_3

open K1_13 (Shape chart mixed32 ceilDiv)
open K1_13_8 (zeroShape)
open P0_9_8 (emptyOrder indexBudget factorCap)
open P0_9 (physicalPrice physicalDegree incidenceGap primaryBox surfaceNumerator32 taylorLength)

/-- The largest admissible top degree for fixed degree and index bounds. -/
def peak (b j : ℕ) : Shape := ⟨b, j, min 10 (j / 3)⟩

private def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P0.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap

private def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P0.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)

private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]

private abbrev RowBound (b j : ℕ) : Prop :=
  physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j

-- The receipt gives main and auxiliary constituents separately. The quotient,
-- the rounded budget and the final comparison are literal Nat arithmetic.
private theorem row (b j l main aux price budget : ℕ)
    (horder : emptyOrder (peak b j) = l) (hmain : mainFee (peak b j) = main)
    (haux : auxFee (peak b j) = aux) (hprice : ceilDiv main l + aux = price)
    (hbudget : indexBudget zeroShape factorCap j = budget) (hle : price ≤ budget) :
    RowBound b j := by
  change physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
  rw [price_eq, horder, hmain, haux, hprice, hbudget]
  exact hle

theorem prices8 (j : ℕ) (hlo : 7 ≤ j) (hhi : j ≤ 24) :
    RowBound 8 j := by
  interval_cases j
  · exact row 8 7 8 13494891631140403 38919532824822 1725780986717373 31278353703198562 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 8 8 19592296916228678 50366978749924 2499404093278509 35746689946512643 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 9 8 30288197588977888 66553615809265 3852578314431501 40215026189826723 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 10 8 44125757190513447 84969284208106 5600688933022287 44683362433140803 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 11 8 59923893929722819 105626392813271 7596113134028624 49151698676454884 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 12 8 78949158367370756 128555474089336 9997200270010681 53620034919768964 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 13 8 101613934854619179 153745174880088 12855487031707486 58088371163083044 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 14 8 128235894562792451 181211140306811 16210697960655868 62556707406397125 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 15 8 159132707738490504 210993333667657 20102581800978970 67025043649711205 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 16 8 194622045090670294 243064459415030 24570820095748817 71493379893025286 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 17 8 235021577790656184 277447567811755 29655144791643778 75961716136339366 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 18 8 280648976085048107 314199928490588 35395321939121602 80430052379653446 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 19 8 331821910682803016 353263833783008 41831002669133385 84898388622967527 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 20 8 388858052755245278 394676552847936 49001933147253596 89366724866281607 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 21 8 452075072548974822 438524060125399 56947908128747252 93835061109595687 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 22 8 521790640772948604 484696939679170 65708527036297746 98303397352909768 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 23 8 598322428598490990 533256796764424 75323560371575798 102771733596223848 rfl rfl rfl rfl rfl (by decide)
  · exact row 8 24 8 681988106272201909 584333890650875 85832847174676114 107240069839537929 rfl rfl rfl rfl rfl (by decide)

theorem prices10 (j : ℕ) (hlo : 13 ≤ j) (hhi : j ≤ 30) :
    RowBound 10 j := by
  interval_cases j
  · exact row 10 13 13 101614031459075621 153747318106536 7970211276496969 58088371163083044 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 14 13 128235999217617752 181213283533259 10045520915657702 62556707406397125 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 15 13 159132820443684664 210995476894105 12451981664869849 67025043649711205 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 16 13 194622165846233312 243066602641478 15214002436967118 71493379893025286 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 17 13 235021706596588061 277449711038203 18356042526160362 75961716136339366 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 18 13 280649112941348842 314202071717036 21902595374897717 80430052379653446 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 19 13 331822055589472610 353265977009456 25878039483891965 84898388622967527 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 20 13 388858205712283730 394678696074384 30306848366250056 89366724866281607 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 21 13 452075233556382133 438526203351847 35213544169227396 93835061109595687 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 22 13 521790809830724774 484699082905618 40622453685269063 98303397352909768 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 23 13 598322605706636018 533258939990872 46558074763578258 102771733596223848 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 24 13 681988291430715796 584336033877323 53044973836240077 107240069839537929 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 25 13 773105537711921063 637739800640792 60107396547711643 111708406082852009 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 26 13 871992015721576184 693570260856577 67769879162516284 116176742326166089 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 27 13 978965395706281090 752022378774376 76057052817719076 120645078569480170 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 28 13 1094343348374992737 812785542032095 84993043109339229 125113414812794250 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 29 13 1218443544899035488 876016886350859 94602443417045897 129581751056108330 rfl rfl rfl rfl rfl (by decide)
  · exact row 10 30 13 1351583655525009275 942001999816655 104909975501740446 134050087299422411 rfl rfl rfl rfl rfl (by decide)

theorem prices21 (j : ℕ) (hlo : 4 ≤ j) (hhi : j ≤ 6) :
    RowBound 21 j := by
  interval_cases j
  · exact row 21 4 1 5743270049328060 27926552906922 5771196602234982 17873344973256321 rfl rfl rfl rfl rfl (by decide)
  · exact row 21 5 1 12671438894218393 41086323168813 12712525217387206 22341681216570401 rfl rfl rfl rfl rfl (by decide)
  · exact row 21 6 1 22392667618785948 55618235379872 22448285854165820 26810017459884482 rfl rfl rfl rfl rfl (by decide)

theorem prices60 (j : ℕ) (hlo : 31 ≤ j) (hhi : j ≤ 40) :
    RowBound 60 j := by
  interval_cases j
  · exact row 60 31 37 2662591686187771276 1423469415854843 73385406880389202 138518423542736491 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 32 37 2849789782606871117 1495070168828268 78516415644689650 142986759786050572 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 33 37 3043807966285618348 1568225548945773 83833305718827350 147455096029364652 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 34 37 3244482933577613815 1642929244833443 89331657179363547 151923432272678732 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 35 37 3451682254803777581 1719174945117363 95007884534408649 156391768515992813 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 36 37 3665273500285033171 1796956338423617 100858402292073163 160860104759306893 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 37 37 3885124240342304110 1876267113378291 106879624960467592 165328441002620973 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 38 37 4111102045296513923 1957100958607469 113067967047702440 169796777245935054 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 39 37 4343074485468586135 2039451562737236 119419843061888213 174265113489249134 rfl rfl rfl rfl rfl (by decide)
  · exact row 60 40 37 4580909131179444271 2123312614393677 125931667511135415 178733449732563215 rfl rfl rfl rfl rfl (by decide)

theorem prices106 (j : ℕ) (hlo : 46 ≤ j) (hhi : j ≤ 48) :
    RowBound 106 j := by
  interval_cases j
  · exact row 106 46 57 10295824129538618604 3705113928213807 184333607428891327 205543467192447697 rfl rfl rfl rfl rfl (by decide)
  · exact row 106 47 57 10757123542002430958 3827044449500748 192548510098666204 210011803435761777 rfl rfl rfl rfl rfl (by decide)
  · exact row 106 48 57 11227286899397429336 3950628476123105 200920574079586778 214480139679075858 rfl rfl rfl rfl rfl (by decide)

theorem prices120 (j : ℕ) (hlo : 3 ≤ j) (hhi : j ≤ 48) :
    RowBound 120 j := by
  interval_cases j
  · exact row 120 3 1 7659480320743281 90591997015806 7750072317759087 13405008729942241 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 4 12 33478483674647244 145357834261938 2935231473815875 17873344973256321 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 5 12 73427521401665077 201786516547943 6320746633353367 22341681216570401 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 6 12 127824012520690932 259905256746454 10911906300137365 26810017459884482 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 7 13 196491375311841009 319687872377625 15434409050211549 31278353703198562 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 8 13 279500028424620484 381142534850236 21881144721359504 35746689946512643 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 9 13 369055189723315224 444328819944417 28833189567891742 40215026189826723 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 10 13 464326958370127248 509167311420806 36226625647584441 44683362433140803 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 11 13 570646770849776521 575689366413985 44471594816396795 49151698676454884 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 12 13 688067438050710024 644018524826989 53572282990266222 53620034919768964 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 13 37 816641771323731762 713962288334425 22785361513300149 58088371163083044 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 14 37 956422582482013150 785603261154978 26634862247155334 62556707406397125 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 15 37 1107462682414001169 859170847255648 30790594696282707 67025043649711205 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 16 37 1269814882470499824 934278834694394 35253599982545741 71493379893025286 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 17 37 1443531994464680530 1011099620610757 40025477849385907 75961716136339366 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 18 37 1628666829284990268 1090020114443999 45108042527551845 80430052379653446 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 19 37 1825272198282233043 1170360090417538 50502041125072486 84898388622967527 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 20 37 2033400913269580270 1252430211648563 56209211651366949 89366724866281607 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 21 37 2253105785135478930 1336835718665726 62231586668273265 93835061109595687 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 22 37 2484439625230733028 1422483517469544 68569500415597464 98303397352909768 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 23 37 2727455245368513979 1509880380173287 75224887011754746 102771733596223848 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 24 37 2982205456437268764 1599919330962530 82200066802240065 107240069839537929 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 25 37 3248743069787801388 1690958113572907 89494824864594567 111708406082852009 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 26 37 3527120897233283266 1783766264835408 97111358081951172 116176742326166089 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 27 37 3817391749662161379 1879602114852082 105052352105721309 120645078569480170 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 28 37 4119608438425239732 1976121625914873 113316890232002434 125113414812794250 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 29 37 4433823775335689740 2074432010738948 121907507019811644 129581751056108330 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 30 37 4760090571281958384 2176241940035967 130827338461169978 134050087299422411 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 31 56 5098461637614849669 2278337764855390 93322295579406277 138518423542736491 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 32 56 5448989786147535010 2382246983149412 99685636021498252 142986759786050572 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 33 56 5811635209102926741 2487963283544119 106267163446096383 147455096029364652 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 34 56 6186234602834625708 2595480354665593 113063955405283910 151923432272678732 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 35 56 6572655537663551974 2704791885139922 120073640771989065 156391768515992813 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 36 56 6970765583910629064 2815891563593189 127293848419140137 160860104759306893 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 37 56 7380432311896780503 2928773078651479 134722207219665417 165328441002620973 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 38 56 7801523291942929816 3043430118940877 142356346046493196 169796777245935054 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 39 56 8233906094370000528 3159856373087469 150193893772551765 174265113489249134 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 40 56 8677448289498916164 3278045529717339 158232479270769414 178733449732563215 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 41 57 9132017447650600249 3397991277456572 163608823692379384 183201785975877295 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 42 57 9597481139145976308 3519687304931253 171896549395211540 187670122219191375 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 43 57 10073706934305967866 3643127300767467 180374827902626553 192138458462505456 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 44 57 10560562403451498448 3768304953591298 189041329575547412 196606794705819536 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 45 57 11057915116903491579 3895213952028832 197893724774897106 201075130949133616 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 46 60 11565632644982870784 4023847984706154 196784392067754001 205543467192447697 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 47 60 12083582558010559588 4154200740249348 205547243373758675 210011803435761777 rfl rfl rfl rfl rfl (by decide)
  · exact row 120 48 60 12611632426307481516 4286265907284499 214480139679075858 214480139679075858 rfl rfl rfl rfl rfl (by decide)

end P0_9_8_3
end PackSource_P0_9_8_3Rows

section PackSource_P0_9_8_3Proof
set_option autoImplicit true
namespace P0_9_8_3

open K1_13 (Shape InBox)
open K1_13_8 (Valid fullCap zeroShape)
open K1_13_8_2 (Threshold orderFor)
open P0_9 (physicalPrice)
open P0_9_8 (emptyOrder emptyThresholds indexBudget factorCap)

/-- A change in order or the last available degree ends an interval. -/
private def endpoint (b j : ℕ) : Prop :=
  b = 120 ∨ emptyOrder (peak b j) ≠ emptyOrder (peak (b + 1) j)

private theorem orderFor_stays (b j : ℕ) (ss : List Threshold)
    (h : ∀ s ∈ ss, s.j ≤ j → s.b ≠ b + 1) :
    orderFor b j ss = orderFor (b + 1) j ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have he : (s.b ≤ b ∧ s.j ≤ j) ↔ (s.b ≤ b + 1 ∧ s.j ≤ j) := by
      constructor
      · exact fun ⟨hb, hj⟩ => ⟨hb.trans (Nat.le_succ _), hj⟩
      · intro ⟨hb, hj⟩
        exact ⟨by have hn := h s List.mem_cons_self hj; omega, hj⟩
    simp only [orderFor, he, ih (fun s hs => h s (List.mem_cons_of_mem _ hs))]

private theorem active_threshold {b j : ℕ}
    (h : emptyOrder (peak b j) ≠ emptyOrder (peak (b + 1) j)) :
    ∃ s ∈ emptyThresholds, s.b = b + 1 ∧ s.j ≤ j := by
  by_contra hn
  apply h
  exact orderFor_stays b j emptyThresholds (fun s hs hj hb => hn ⟨s, hs, hb, hj⟩)

private theorem endpoint_bound {b j : ℕ} (hj : 3 ≤ j) (hmax : j ≤ 48)
    (hshape : j ≤ 3 * b) (he : endpoint b j) :
    physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j := by
  rcases he with rfl | hchange
  · exact prices120 j hj hmax
  obtain ⟨s, hs, hb, hjs⟩ := active_threshold hchange
  simp [emptyThresholds] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 107 = b + 1 at hb
    change 46 ≤ j at hjs
    have hb' : b = 106 := by omega
    subst b
    have hjt : j ≤ 48 := by omega
    interval_cases j
    · exact prices106 46 (by decide) (by decide)
    · exact prices106 47 (by decide) (by decide)
    · exact prices106 48 (by decide) (by decide)
  · change 14 = b + 1 at hb
    change 41 ≤ j at hjs
    omega
  · change 61 = b + 1 at hb
    change 31 ≤ j at hjs
    have hb' : b = 60 := by omega
    subst b
    have hjt : j ≤ 48 := by omega
    interval_cases j
    · exact prices60 31 (by decide) (by decide)
    · exact prices60 32 (by decide) (by decide)
    · exact prices60 33 (by decide) (by decide)
    · exact prices60 34 (by decide) (by decide)
    · exact prices60 35 (by decide) (by decide)
    · exact prices60 36 (by decide) (by decide)
    · exact prices60 37 (by decide) (by decide)
    · exact prices60 38 (by decide) (by decide)
    · exact prices60 39 (by decide) (by decide)
    · exact prices60 40 (by decide) (by decide)
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
  · change 11 = b + 1 at hb
    change 13 ≤ j at hjs
    have hb' : b = 10 := by omega
    subst b
    have hjt : j ≤ 30 := by omega
    interval_cases j
    · exact prices10 13 (by decide) (by decide)
    · exact prices10 14 (by decide) (by decide)
    · exact prices10 15 (by decide) (by decide)
    · exact prices10 16 (by decide) (by decide)
    · exact prices10 17 (by decide) (by decide)
    · exact prices10 18 (by decide) (by decide)
    · exact prices10 19 (by decide) (by decide)
    · exact prices10 20 (by decide) (by decide)
    · exact prices10 21 (by decide) (by decide)
    · exact prices10 22 (by decide) (by decide)
    · exact prices10 23 (by decide) (by decide)
    · exact prices10 24 (by decide) (by decide)
    · exact prices10 25 (by decide) (by decide)
    · exact prices10 26 (by decide) (by decide)
    · exact prices10 27 (by decide) (by decide)
    · exact prices10 28 (by decide) (by decide)
    · exact prices10 29 (by decide) (by decide)
    · exact prices10 30 (by decide) (by decide)
  · change 9 = b + 1 at hb
    change 7 ≤ j at hjs
    have hb' : b = 8 := by omega
    subst b
    have hjt : j ≤ 24 := by omega
    interval_cases j
    · exact prices8 7 (by decide) (by decide)
    · exact prices8 8 (by decide) (by decide)
    · exact prices8 9 (by decide) (by decide)
    · exact prices8 10 (by decide) (by decide)
    · exact prices8 11 (by decide) (by decide)
    · exact prices8 12 (by decide) (by decide)
    · exact prices8 13 (by decide) (by decide)
    · exact prices8 14 (by decide) (by decide)
    · exact prices8 15 (by decide) (by decide)
    · exact prices8 16 (by decide) (by decide)
    · exact prices8 17 (by decide) (by decide)
    · exact prices8 18 (by decide) (by decide)
    · exact prices8 19 (by decide) (by decide)
    · exact prices8 20 (by decide) (by decide)
    · exact prices8 21 (by decide) (by decide)
    · exact prices8 22 (by decide) (by decide)
    · exact prices8 23 (by decide) (by decide)
    · exact prices8 24 (by decide) (by decide)
  · change 22 = b + 1 at hb
    change 4 ≤ j at hjs
    have hb' : b = 21 := by omega
    subst b
    have hjt : j ≤ 48 := by omega
    interval_cases j
    · exact prices21 4 (by decide) (by decide)
    · exact prices21 5 (by decide) (by decide)
    · exact prices21 6 (by decide) (by decide)
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
    · exact (hchange (by decide)).elim
  · change 3 = b + 1 at hb
    change 7 ≤ j at hjs
    omega

private theorem peak_fits_index (b j : ℕ) : 3 * (peak b j).t ≤ j := by
  have h := min_le_right 10 (j / 3)
  change 3 * min 10 (j / 3) ≤ j
  omega

-- Port the decreasing induction on degree from the light 69.15 price proof.
private theorem peak_bound (b j : ℕ) (hb : b ≤ 120) (hshape : j ≤ 3 * b)
    (hend : ∀ k ≤ 120, j ≤ 3 * k → endpoint k j →
      physicalPrice (peak k j) (emptyOrder (peak k j)) ≤ indexBudget zeroShape factorCap j) :
    physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j := by
  induction hb using Nat.decreasingInduction with
  | self => exact hend _ le_rfl hshape (Or.inl rfl)
  | of_succ b hb ih =>
    by_cases he : endpoint b j
    · exact hend b (by omega) hshape he
    · have horder : emptyOrder (peak b j) = emptyOrder (peak (b + 1) j) := by
        by_contra h
        exact he (Or.inr h)
      have hmono : InBox (peak b j) (peak (b + 1) j) :=
        ⟨Nat.le_succ b, le_rfl, le_rfl⟩
      rw [horder]
      exact (physical_mono hmono (peak_fits_index b j) (peak_fits_index (b + 1) j) _).trans
        (ih (by omega))

theorem proof : P0_9_8.c3 := by
  intro a ha hbox
  have hz : zeroShape.plus a = a := by
    cases a
    simp [zeroShape, Shape.plus]
  rw [hz] at hbox
  have hj : 3 ≤ a.j := (Nat.mul_le_mul_left 3 ha.1).trans ha.2.1
  have hmax : a.j ≤ 48 := hbox.2.1
  have ht : a.t ≤ (peak a.b a.j).t :=
    le_min hbox.2.2 ((Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
      (by simpa [Nat.mul_comm] using ha.2.1))
  have hmono : InBox a (peak a.b a.j) := ⟨le_rfl, le_rfl, ht⟩
  have horder : emptyOrder a = emptyOrder (peak a.b a.j) := rfl
  rw [horder]
  exact (physical_mono hmono ha.2.1 (peak_fits_index a.b a.j) _).trans <|
    peak_bound _ _ hbox.1 ha.2.2 fun _ _ hvalid he =>
      endpoint_bound hj hmax hvalid he

end P0_9_8_3
end PackSource_P0_9_8_3Proof

section PackSource_P0_9_8_4Proof
set_option autoImplicit true
namespace P0_9_8_4

open K1_13 (Shape)
open K1_13_8 (availableMass availableMass_eq_sum availableMass_mono fastRemaining
  layerTerm remaining_anti)
open P0_9_8 (availableMass_anti_prefix oneOrder oneStart symbol_count)
open scoped BigOperators

/-- At layer k + 1, spend the retained resource in every layer and the
positive index only after its proposed order predecessor L. -/
private def capacity (j L k : ℕ) : ℕ :=
  fastRemaining (k + 1) ((k + 1) * 3 + (k + 1 - L) * j)

private theorem capacity_anti (j L : ℕ) : Antitone (capacity j L) := by
  intro a b hab
  simp only [capacity, ← symbol_count]
  exact remaining_anti (by omega) <|
    Nat.add_le_add (Nat.mul_le_mul_right 3 (by omega))
      (Nat.mul_le_mul_right j (by omega))

private def layerMass (j L s n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, capacity j L (s + k)

private theorem mass_eq (j L : ℕ) :
    availableMass oneStart ⟨0, j, 0⟩ L = layerMass j L 0 (L + 1650 / (3 + j)) := by
  have h := availableMass_eq_sum symbol_count (r := oneStart)
    (y := ⟨0, j, 0⟩) (L := L) (N := L + 1650 / (3 + j))
    (Or.inr (by decide)) (by change 0 < 3 + j; omega) le_rfl
  rw [← h]
  change (∑ k ∈ Finset.range _, K1_13.remaining
    ((k + 1) * 1 + (k + 1 - L) * 0) ((k + 1) * 3 + (k + 1 - L) * j)) = _
  simp only [layerMass, capacity, symbol_count, Nat.zero_add, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero]

/-- Bound a block by its first layer and add a certified bound for the rest. -/
private theorem add_block (width count rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hcount : capacity j L s ≤ count)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest)
    (htotal : width * count + rest ≤ cap) : layerMass j L s n ≤ cap := by
  have hsplit : layerMass j L s n =
      layerMass j L s width + layerMass j L (s + width) (n - width) := by
    conv_lhs => rw [layerMass, ← Nat.add_sub_of_le hw, Finset.sum_range_add]
    simp only [layerMass, Nat.add_assoc]
  have hblock : layerMass j L s width ≤ width * count := by
    calc
      _ ≤ ∑ _k ∈ Finset.range width, count :=
        Finset.sum_le_sum fun k _ =>
          ((capacity_anti j L) (Nat.le_add_right s k)).trans hcount
      _ = _ := by simp
  rw [hsplit]
  exact (Nat.add_le_add hblock hrest).trans htotal

-- Each sample is one inherited two-budget count. All block totals use literal arithmetic.
private theorem check4 : availableMass oneStart ⟨0, 4, 0⟩ 7 < P0_9.layerNeed := by
  have hmass : layerMass 4 7 0 242 ≤ 26690408097132 := by
    refine add_block 3 406784167900 25470055593432 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 400304151070 24269143140222 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 393891787720 23481359564782 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 384364770210 22712630024362 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 374983310625 21962663403112 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 365746614030 21231170175052 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 356653873940 20517862427172 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 347704279260 19822453868652 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 338897010819 19144659847014 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 330231237888 18484197371238 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 321706125136 17840785120966 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 313320829156 17214143462654 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 305074494975 16603994472704 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 296966263026 16010061946652 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 288995265666 15432071415320 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 281160623678 14869750167964 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 273461453259 14322827261446 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 265896862530 13791033536386 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 258465948030 13274101640326 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 251167801720 12771766036886 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 244001507485 12283763021916 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 236966137620 11809830746676 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 230060759850 11349709226976 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 223284433824 10903140359328 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 216636207593 10469867944142 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 210115124646 10049637694850 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 203720220396 9438477033662 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 194362313625 8855390092787 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 185282791606 8299541717969 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 176478294294 7770106835087 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 167945417415 7266270582842 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 159680719126 6787228425464 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 151680713340 6332186285444 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 143941876416 5900360656196 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 136460640454 5490978734834 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 129233400015 5103278534789 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 122256505386 4736509018631 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 115526269330 4389930210641 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 109038960321 4062813329678 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 102790809324 3754440901706 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 96778003000 3464106892706 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 90996690516 3191116821158 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 85442976720 2934787890998 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 80112928981 2694449104055 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 75002570334 2469441393053 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 70107886350 2189009847653 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 63910114160 1933369391013 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 58078816180 1701054126293 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 52604132104 1490637597877 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 47476072346 1300733308493 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 42684521670 1129995221813 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 38219231946 977118294029 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 34069825764 840838990973 (by decide) (by decide) ?_ (by decide)
    refine add_block 5 30225800080 689709990573 (by decide) (by decide) ?_ (by decide)
    refine add_block 5 25833992566 560540027743 (by decide) (by decide) ?_ (by decide)
    refine add_block 5 21881661009 451131722698 (by decide) (by decide) ?_ (by decide)
    refine add_block 5 18347430560 359394569898 (by decide) (by decide) ?_ (by decide)
    refine add_block 6 15209617976 268136862042 (by decide) (by decide) ?_ (by decide)
    refine add_block 6 11936512409 196517787588 (by decide) (by decide) ?_ (by decide)
    refine add_block 7 9163928850 132370285638 (by decide) (by decide) ?_ (by decide)
    refine add_block 8 6509420778 80294919414 (by decide) (by decide) ?_ (by decide)
    refine add_block 9 4162910070 42828728784 (by decide) (by decide) ?_ (by decide)
    refine add_block 12 2283527054 15426404136 (by decide) (by decide) ?_ (by decide)
    refine add_block 19 794259840 335467176 (by decide) (by decide) ?_ (by decide)
    refine add_block 12 27955598 0 (by decide) (by decide) ?_ (by decide)
    change layerMass 4 7 _ 0 ≤ 0
    simp [layerMass]
  rw [mass_eq]
  exact hmass.trans_lt (by decide)


private theorem check8 : availableMass oneStart ⟨0, 8, 0⟩ 40 < P0_9.layerNeed := by
  have hmass : layerMass 8 40 0 190 ≤ 26690904870288 := by
    refine add_block 3 406784167900 25470552366588 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 400304151070 24269639913378 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 393891787720 23087964550218 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 387546758098 21925324275924 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 381268738714 20781518059782 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 375057408724 19656345833610 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 368912443543 18549608502981 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 362833521235 17461107939276 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 356820316120 16390646990916 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 350872505170 14987156970236 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 343043250940 13614983966476 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 335328901134 12273668361940 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 327728681728 11618210998484 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 314600379282 10989010239920 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 301804249016 10385401741888 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 289337397405 9806726947078 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 277196873536 9252333200006 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 265379672598 8721573854810 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 253882728918 8213808396974 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 242702919435 7728402558104 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 231837067206 7264728423692 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 221281934410 6822164554872 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 211034225838 6400096103196 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 201090592415 5997914918366 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 191447624172 5615019670022 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 182101853752 5250815962518 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 173049759948 4904716442622 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 164287760643 4576140921336 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 155812216332 4264516488672 (by decide) (by decide) ?_ (by decide)
    refine add_block 2 147619433676 3969277621320 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 139705658410 3550160646090 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 128349782268 3165111299286 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 117599984208 2812311346662 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 107442869650 2489982737712 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 97864756920 2196388466952 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 88851670443 1929833455623 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 80389347577 1688665412892 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 72463231752 1471275717636 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 65058479358 1276100279562 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 58159952830 1101620421072 (by decide) (by decide) ?_ (by decide)
    refine add_block 3 51752227590 946363738302 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 45819585078 763085397990 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 38620705398 608602576398 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 32199181326 479805851094 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 26515349428 373744453382 (by decide) (by decide) ?_ (by decide)
    refine add_block 5 21528624500 266101330882 (by decide) (by decide) ?_ (by decide)
    refine add_block 5 16212216748 185040247142 (by decide) (by decide) ?_ (by decide)
    refine add_block 6 11837052450 114017932442 (by decide) (by decide) ?_ (by decide)
    refine add_block 7 7709019570 60054795452 (by decide) (by decide) ?_ (by decide)
    refine add_block 8 4248004390 26070760332 (by decide) (by decide) ?_ (by decide)
    refine add_block 12 1773911422 4783823268 (by decide) (by decide) ?_ (by decide)
    refine add_block 23 207992316 0 (by decide) (by decide) ?_ (by decide)
    change layerMass 8 40 _ 0 ≤ 0
    simp [layerMass]
  rw [mass_eq]
  exact hmass.trans_lt (by decide)


private theorem check30 : availableMass oneStart ⟨0, 30, 0⟩ 64 < P0_9.layerNeed := by
  have hmass : layerMass 30 64 0 114 ≤ 27032649695246 := by
    refine add_block 10 406784167900 22964808016246 (by decide) (by decide) ?_ (by decide)
    refine add_block 10 385446654945 19110341466796 (by decide) (by decide) ?_ (by decide)
    refine add_block 10 364852510390 15461816362896 (by decide) (by decide) ?_ (by decide)
    refine add_block 10 344989761610 12011918746796 (by decide) (by decide) ?_ (by decide)
    refine add_block 10 325846368480 8753455061996 (by decide) (by decide) ?_ (by decide)
    refine add_block 10 307410223375 5679352828246 (by decide) (by decide) ?_ (by decide)
    refine add_block 4 289669151170 4520676223566 (by decide) (by decide) ?_ (by decide)
    refine add_block 9 266785774535 2119604252751 (by decide) (by decide) ?_ (by decide)
    refine add_block 9 137697708645 880324874946 (by decide) (by decide) ?_ (by decide)
    refine add_block 9 57290520224 364710192930 (by decide) (by decide) ?_ (by decide)
    refine add_block 23 15856964910 0 (by decide) (by decide) ?_ (by decide)
    change layerMass 30 64 _ 0 ≤ 0
    simp [layerMass]
  rw [mass_eq]
  exact hmass.trans_lt (by decide)

private theorem check_interval {j lo L : ℕ} (hj : lo ≤ j)
    (hL : oneOrder ⟨0, j, 0⟩ - 1 ≤ L)
    (hcheck : availableMass oneStart ⟨0, lo, 0⟩ L < P0_9.layerNeed) :
    availableMass oneStart ⟨0, j, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) < P0_9.layerNeed := by
  have hstart : oneStart = K1_13_8.zeroShape ∨ 0 < oneStart.j := Or.inr (by decide)
  have hindex : 0 < oneStart.j + (⟨0, lo, 0⟩ : Shape).j := by
    change 0 < 3 + lo
    omega
  calc
    availableMass oneStart ⟨0, j, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) ≤
        availableMass oneStart ⟨0, lo, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) :=
      availableMass_anti_prefix hstart hindex (Nat.zero_le 0) hj
    _ ≤ availableMass oneStart ⟨0, lo, 0⟩ L :=
      availableMass_mono symbol_count hstart hindex hL
    _ < P0_9.layerNeed := hcheck

theorem proof : P0_9_8.c4 := by
  intro j hj4 hj45
  have horder : oneOrder ⟨0, j, 0⟩ - 1 = (3 * j - 4) / 2 - 1 := by
    have hj : ¬ j ≤ 3 := by omega
    simp only [oneOrder, ite_eq_right hj]
  by_cases hj7 : j ≤ 7
  · exact check_interval hj4 (by rw [horder]; omega) check4
  by_cases hj29 : j ≤ 29
  · exact check_interval (by omega) (by rw [horder]; omega) check8
  exact check_interval (by omega) (by rw [horder]; omega) check30

end P0_9_8_4
end PackSource_P0_9_8_4Proof

section PackSource_P0_9_8_5Mono
set_option autoImplicit true
namespace P0_9_8_5

open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open P0_9 (physicalPrice physicalDegree incidenceGap primaryBox taylorLength surfaceNumerator32)

private theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩

private theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩

private theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩

private theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩

private theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩

private theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩

private theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩

private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega

private theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
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
    surfaceNumerator32 p q ≤ surfaceNumerator32 p' q := by
  let L := taylorLength
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

/-- The retuned physical tariff is monotone in the three factor caps at fixed order. -/
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : physicalPrice x l ≤ physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q := primaryBox
  let L := taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := by dsimp [Chamber, q]; omega
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (P0.t + 2*incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P0.t + 2*incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P0.t hc) (Nat.mul_le_mul_left (2*incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)

end P0_9_8_5
end PackSource_P0_9_8_5Mono

section PackSource_P0_9_8_5Proof
set_option autoImplicit true
namespace P0_9_8_5

open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open P0_9 (physicalPrice primaryBox taylorLength surfaceNumerator32)
open P0_9_8 (oneStart oneOrder indexBudget factorCap oneReserve)

private def peak (j : ℕ) : Shape := ⟨119, j, min 9 (j / 3)⟩

private def peakPrice (j : ℕ) : Prop :=
  physicalPrice (peak j) (oneOrder (peak j)) ≤ indexBudget oneStart (factorCap - oneReserve) j

private def graphShape_P0_9_8_5Proof (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩

private theorem surface_ordinary {p : Shape} {n : ℕ}
    (h : mixed32 p primaryBox (chart (taylorLength + 1) p) (chart (taylorLength + 2) p) = n) :
    surfaceNumerator32 p primaryBox ≤ n :=
  (min_le_left _ _).trans_eq h

private theorem surface_lifted {p : Shape} {n₀ n₁ n₂ : ℕ}
    (h₀ : mixed32 p primaryBox (liftedChart (taylorLength + 1) p)
      (liftedChart (taylorLength + 2) p) = n₀)
    (h₁ : mixed32 p primaryBox (graphShape_P0_9_8_5Proof p) (liftedChart (taylorLength + 2) p) = n₁)
    (h₂ : mixed32 p primaryBox (graphShape_P0_9_8_5Proof p) (liftedChart (taylorLength + 1) p) = n₂) :
    surfaceNumerator32 p primaryBox ≤ n₀ + 133553 * n₁ + 133554 * n₂ := by
  calc
    _ ≤ mixed32 p primaryBox (liftedChart (taylorLength + 1) p) (liftedChart (taylorLength + 2) p) +
        133553 * mixed32 p primaryBox (graphShape_P0_9_8_5Proof p) (liftedChart (taylorLength + 2) p) +
        133554 * mixed32 p primaryBox (graphShape_P0_9_8_5Proof p) (liftedChart (taylorLength + 1) p) :=
      min_le_right _ _
    _ = _ := by rw [h₀, h₁, h₂]

private structure PriceParts where
  surface : ℕ
  chartDegree : ℕ
  curvesBank : ℕ
  curvesSelf : ℕ
  pointsBank : ℕ
  pointsSelf : ℕ

/-- Transport constituent checks to a price comparison on natural-number literals. -/
private theorem peak_le_of_parts (j top order : ℕ) (v : PriceParts)
    (htop : (peak j).t = top) (horder : oneOrder (peak j) = order)
    (hs : surfaceNumerator32 (peak j).chamber primaryBox ≤ v.surface)
    (hb : (chart (taylorLength + 1) (peak j).chamber).b = v.chartDegree)
    (hc₁ : mixed32 (peak j).chamber primaryBox (primaryBox.plus ((peak j).chamber.scale 4))
      (chart taylorLength (peak j).chamber) = v.curvesBank)
    (hc₂ : mixed32 (peak j).chamber (peak j).chamber (peak j).chamber
      (chart taylorLength (peak j).chamber) = v.curvesSelf)
    (hp₁ : mixed32 (peak j).chamber primaryBox (primaryBox.plus ((peak j).chamber.scale 4))
      (peak j).chamber = v.pointsBank)
    (hp₂ : mixed32 (peak j).chamber (peak j).chamber (peak j).chamber
      (peak j).chamber = v.pointsSelf)
    (h : ceilDiv (ceilDiv v.surface 32 +
        ceilDiv ((81936 + 2 * 46657) * 119 * 4012 * v.chartDegree) 46657) order +
        2 * 133551 * 119 * 4012 +
        ceilDiv (81936 * (v.curvesBank + 2 * top * v.curvesSelf) +
          2 * 46657 * (v.pointsBank + 2 * top * v.pointsSelf)) (32 * 46657) ≤
      177480139679075858 * j / 45) :
    peakPrice j := by
  unfold peakPrice physicalPrice
  dsimp only
  rw [horder, hb, hc₁, hc₂, hp₁, hp₂, htop]
  have hmain := ceil_mono (Nat.add_le_add_right (ceil_mono hs 32)
    (ceilDiv ((81936 + 2 * 46657) * 119 * 4012 * v.chartDegree) 46657)) order
  exact (Nat.add_le_add_right (Nat.add_le_add_right hmain _) _).trans h

section
set_option maxRecDepth 4096

-- Each equality supplied by rfl checks one constituent at the given index.
private theorem peakPrice3 : peakPrice 3 :=
  peak_le_of_parts 3 1 1
    ⟨241223472693437664, 31518509, 1634695628625120, 6791971272, 10876866912, 67752⟩ rfl rfl
    (surface_ordinary (n := 241223472693437664) rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice4 : peakPrice 4 :=
  peak_le_of_parts 4 1 4
    ⟨1060525244545298880, 31518509, 2624686164684864, 22545804288, 14729235328, 157464⟩ rfl rfl
    (surface_ordinary (n := 1060525244545298880) rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice5 : peakPrice 5 :=
  peak_le_of_parts 5 1 5
    ⟨2328221039645949536, 31518509, 3644899368963104, 48646188696, 18694781152, 291240⟩ rfl rfl
    (surface_ordinary (n := 2328221039645949536) rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice6 : peakPrice 6 :=
  peak_le_of_parts 6 2 7
    ⟨4054468266600002496, 31518509, 4695605713107072, 98414135040, 22775181696, 535680⟩ rfl rfl
    (surface_ordinary (n := 4054468266600002496) rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice7 : peakPrice 7 :=
  peak_le_of_parts 7 2 8
    ⟨6233616310371176160, 31518509, 5776602215171424, 165599409576, 26968790752, 844800⟩ rfl rfl
    (surface_ordinary (n := 6233616310371176160) rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice8 : peakPrice 8 :=
  peak_le_of_parts 8 2 10
    ⟨8867918567743636160, 31518509, 6887922620007104, 254420118528, 31275956224, 1239936⟩ rfl rfl
    (surface_ordinary (n := 8867918567743636160) rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice9 : peakPrice 9 :=
  peak_le_of_parts 9 3 11
    ⟨11710457961904499040, 31518509, 8029837399261344, 377928031608, 35698355424, 1786536⟩ rfl rfl
    (surface_lifted (n₀ := 3290124804054760480) (n₁ := 31524313040320) (n₂ := 31524076990400) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice10 : peakPrice 10 :=
  peak_le_of_parts 10 3 13
    ⟨14734198860188463808, 31518509, 9202143570988800, 529770347136, 40234342144, 2438424⟩ rfl rfl
    (surface_lifted (n₀ := 4218648037054968320) (n₁ := 39368456079040) (n₂ := 39368161256192) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice11 : peakPrice 11 :=
  peak_le_of_parts 11 3 14
    ⟨18108651994636255744, 31518509, 10404874880040416, 713972856456, 44884264288, 3216168⟩ rfl rfl
    (surface_lifted (n₀ := 5263487621307875552) (n₁ := 48090137904160) (n₂ := 48089777811328) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice12 : peakPrice 12 :=
  peak_le_of_parts 12 4 16
    ⟨21835507313678178240, 31518509, 11638301798063424, 943318088448, 49649799168, 4184064⟩ rfl rfl
    (surface_lifted (n₀ := 6425206863828886528) (n₁ := 57693576527296) (n₂ := 57693144525056) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice13 : peakPrice 13 :=
  peak_le_of_parts 13 4 17
    ⟨25916454780539959456, 31518509, 12902221343112480, 1211350673496, 54529300576, 5295744⟩ rfl rfl
    (surface_lifted (n₀ := 7704369071633184032) (n₁ := 68182989960064) (n₂ := 68182479377408) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice14 : peakPrice 14 :=
  peak_le_of_parts 14 4 19
    ⟨30353184373243084672, 31518509, 14196667260038528, 1521904088064, 59523116416, 6571008⟩ rfl rfl
    (surface_lifted (n₀ := 9101537551736061632) (n₁ := 79562596214080) (n₂ := 79562000459200) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice15 : peakPrice 15 :=
  peak_le_of_parts 15 5 20
    ⟨35147386040217857280, 31518509, 15521910020488800, 1887491620200, 64632924000, 8073000⟩ rfl rfl
    (surface_lifted (n₀ := 10617275611152923680) (n₁ := 91836613300960) (n₂ := 91835925639680) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice16 : peakPrice 16 :=
  peak_le_of_parts 16 5 22
    ⟨40300749744690005440, 31518509, 16877746642517952, 2301555332352, 69857077120, 9755160⟩ rfl rfl
    (surface_lifted (n₀ := 12252146556898952960) (n₁ := 105009259232320) (n₂ := 105008472898880) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice17 : peakPrice 17 :=
  peak_le_of_parts 17 5 23
    ⟨45814965464681014432, 31518509, 18264210870976928, 2767736386104, 75195923680, 11636520⟩ rfl rfl
    (surface_lifted (n₀ := 14006713695989443040) (n₁ := 119084752019776) (n₂ := 119083860327616) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice18 : peakPrice 18 :=
  peak_le_of_parts 18 6 25
    ⟨51691723148621187648, 31518509, 19681573177512960, 3298278828672, 80651140992, 13779072⟩ rfl rfl
    (surface_lifted (n₀ := 15881540335439798272) (n₁ := 134067309674944) (n₂ := 134066305795136) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice19 : peakPrice 19 :=
  peak_le_of_parts 19 6 26
    ⟨57932712759736253248, 31518509, 21129630580180704, 3886522154568, 86221082848, 16136064⟩ rfl rfl
    (surface_lifted (n₀ := 17877189782265201440) (n₁ := 149961150209440) (n₂ := 149960027281472) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice20 : peakPrice 20 :=
  peak_le_of_parts 20 6 28
    ⟨64539624276047696512, 31518509, 22608416823831104, 4535915210496, 91906097152, 18725760⟩ rfl rfl
    (surface_lifted (n₀ := 19994225343480946112) (n₁ := 166770491634880) (n₂ := 166769242877440) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice21 : peakPrice 21 :=
  peak_le_of_parts 21 7 29
    ⟨71514147645985820832, 31518509, 24118202380111392, 5258432802840, 97707861216, 21609000⟩ rfl rfl
    (surface_lifted (n₀ := 22233210326102436640) (n₁ := 184499551962880) (n₂ := 184498170452288) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice22 : peakPrice 22 :=
  peak_le_of_parts 22 7 31
    ⟨78857972832776354368, 31518509, 25658784267076224, 6047311858176, 103624728832, 24738840⟩ rfl rfl
    (surface_lifted (n₀ := 24594708037144855808) (n₁ := 203152549205056) (n₂ := 203151027986048) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice23 : peakPrice 23 :=
  peak_le_of_parts 23 7 32
    ⟨86572789814440782400, 31518509, 27230196229576544, 6905808908328, 109657047904, 28132776⟩ rfl rfl
    (surface_lifted (n₀ := 27079281783623497184) (n₁ := 222733701373024) (n₂ := 222732033569536) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice24 : peakPrice 24 :=
  peak_le_of_parts 24 8 34
    ⟨94660288539409408320, 31518509, 28832708739259584, 7845629518848, 115806495744, 31850496⟩ rfl rfl
    (surface_lifted (n₀ := 29687494872553765120) (n₁ := 243247226478400) (n₂ := 243245405072000) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice25 : peakPrice 25 :=
  peak_le_of_parts 25 8 35
    ⟨103122158970907960288, 31518509, 30466118814180000, 8859908048376, 122071426144, 35844864⟩ rfl rfl
    (surface_lifted (n₀ := 32419910610950842400) (n₁ := 264697342532800) (n₂ := 264695360473472) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice26 : peakPrice 26 :=
  peak_le_of_parts 26 8 37
    ⟨111960091086957923584, 31518509, 32130460199188736, 9951708713856, 128452187008, 40132608⟩ rfl rfl
    (surface_lifted (n₀ := 35277092305830022592) (n₁ := 287088267547840) (n₂ := 287086117864768) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice27 : peakPrice 27 :=
  peak_le_of_parts 27 9 38
    ⟨121175774835989601600, 31518509, 33826003365933024, 11132467840008, 134950455648, 44772264⟩ rfl rfl
    (surface_lifted (n₀ := 38259603264206710048) (n₁ := 310424219535136) (n₂ := 310421895115136) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice28 : peakPrice 28 :=
  peak_le_of_parts 28 9 40
    ⟨130770900181228722496, 31518509, 35552545332467520, 12395217217536, 141564585856, 49716504⟩ rfl rfl
    (surface_lifted (n₀ := 41368006793096087552) (n₁ := 334709416506304) (n₂ := 334706910204608) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice29 : peakPrice 29 :=
  peak_le_of_parts 29 9 41
    ⟨140747157100696771552, 31518509, 37310119843643168, 13742828748504, 148294925536, 54981288⟩ rfl rfl
    (surface_lifted (n₀ := 44602866199513448672) (n₁ := 359948076472960) (n₂ := 359945381224000) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice30 : peakPrice 30 :=
  peak_le_of_parts 30 9 43
    ⟨151103271745526943456, 31518509, 39098642280912768, 15173936997120, 155141157888, 60561432⟩ rfl rfl
    (surface_lifted (n₀ := 47963756892563064256) (n₁ := 386137020011296) (n₂ := 386134128662528) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice31 : peakPrice 31 :=
  peak_le_of_parts 31 9 44
    ⟨161834018399034465280, 31518509, 40918028025729120, 16687176527592, 162102966112, 66451752⟩ rfl rfl
    (surface_lifted (n₀ := 51448937005228161056) (n₁ := 413263204154848) (n₂ := 413260109688320) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice32 : peakPrice 32 :=
  peak_le_of_parts 32 9 46
    ⟨172935159311488779040, 31518509, 42768192459545024, 18281181904128, 169180033408, 72647064⟩ rfl rfl
    (surface_lifted (n₀ := 55056993989521949888) (n₁ := 441316051822816) (n₂ := 441312747299776) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice33 : peakPrice 33 :=
  peak_le_of_parts 33 9 47
    ⟨184402456733159437536, 31518509, 44649050963813280, 19954587690936, 176372042976, 79142184⟩ rfl rfl
    (surface_lifted (n₀ := 58786515297457752352) (n₁ := 470284985934400) (n₂ := 470281464495296) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice34 : peakPrice 34 :=
  peak_le_of_parts 34 9 49
    ⟨196231672914315993568, 31518509, 46560518919986688, 21706028452224, 183678678016, 85931928⟩ rfl rfl
    (surface_lifted (n₀ := 62636088381048890048) (n₁ := 500159429408800) (n₂ := 500155684273280) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice35 : peakPrice 35 :=
  peak_le_of_parts 35 9 50
    ⟨208418570105227999936, 31518509, 48502511709518048, 23534138752200, 191099621728, 93011112⟩ rfl rfl
    (surface_lifted (n₀ := 66604300692308684576) (n₁ := 530928805165216) (n₂ := 530924829632128) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice36 : peakPrice 36 :=
  peak_le_of_parts 36 9 52
    ⟨220958910556165009440, 31518509, 50474944713860160, 25437553155072, 198634557312, 100374552⟩ rfl rfl
    (surface_lifted (n₀ := 70689739683250457536) (n₁ := 562582536122848) (n₂ := 562578323570240) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice37 : peakPrice 37 :=
  peak_le_of_parts 37 9 53
    ⟨233848456517396574880, 31518509, 52477733314465824, 27414906225048, 206283167968, 108017064⟩ rfl rfl
    (surface_lifted (n₀ := 74890992805887530528) (n₁ := 595110045200896) (n₂ := 595105589086016) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice38 : peakPrice 38 :=
  peak_le_of_parts 38 9 55
    ⟨247082970239192249056, 31518509, 54510792892787840, 29464832526336, 214045136896, 115933464⟩ rfl rfl
    (surface_lifted (n₀ := 79206647512233225152) (n₁ := 628500755318560) (n₂ := 628496049177856) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice39 : peakPrice 39 :=
  peak_le_of_parts 39 9 56
    ⟨260658213971821584768, 31518509, 56574038830279008, 31585966623144, 221920147296, 124118568⟩ rfl rfl
    (surface_lifted (n₀ := 83635291254300863008) (n₁ := 662744089395040) (n₂ := 662739126844160) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice40 : peakPrice 40 :=
  peak_le_of_parts 40 9 58
    ⟨274569949965554134816, 31518509, 58667386508392128, 33776943079680, 229907882368, 132567192⟩ rfl rfl
    (surface_lifted (n₀ := 88175511484103765696) (n₁ := 697829470349536) (n₂ := 697824245083328) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice41 : peakPrice 41 :=
  peak_le_of_parts 41 9 59
    ⟨288813940470659452000, 31518509, 60790751308580000, 36036396460152, 238008025312, 141274152⟩ rfl rfl
    (surface_lifted (n₀ := 92825895653655254816) (n₁ := 733746321101248) (n₂ := 733740826893760) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice42 : peakPrice 42 :=
  peak_le_of_parts 42 9 61
    ⟨303385947737407089120, 31518509, 62944048612295424, 38362961328768, 246220259328, 150234264⟩ rfl rfl
    (surface_lifted (n₀ := 97585031214968651968) (n₁ := 770484064569376) (n₂ := 770478295273856) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice43 : peakPrice 43 :=
  peak_le_of_parts 43 9 62
    ⟨318281734016066598976, 31518509, 65127193800991200, 40755272249736, 254544267616, 159442344⟩ rfl rfl
    (surface_lifted (n₀ := 102451505620057278752) (n₁ := 808032123673120) (n₂ := 808026073222016) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice44 : peakPrice 44 :=
  peak_le_of_parts 44 9 64
    ⟨333497061556907534368, 31518509, 67340102256120128, 43211963787264, 262979733376, 168893208⟩ rfl rfl
    (surface_lifted (n₀ := 107423906320934456768) (n₁ := 846379921331680) (n₂ := 846373583736640) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem peakPrice45 : peakPrice 45 :=
  peak_le_of_parts 45 9 65
    ⟨349027692610199448096, 31518509, 69582689359135008, 45731670505560, 271526339808, 178581672⟩ rfl rfl
    (surface_lifted (n₀ := 112500820769613507616) (n₁ := 885516880464256) (n₂ := 885510249816128) rfl rfl rfl)
    rfl rfl rfl rfl rfl (by decide)

private theorem prices_at_cap (j : Fin 43) : peakPrice (j.val + 3) := by
  fin_cases j
  · exact peakPrice3
  · exact peakPrice4
  · exact peakPrice5
  · exact peakPrice6
  · exact peakPrice7
  · exact peakPrice8
  · exact peakPrice9
  · exact peakPrice10
  · exact peakPrice11
  · exact peakPrice12
  · exact peakPrice13
  · exact peakPrice14
  · exact peakPrice15
  · exact peakPrice16
  · exact peakPrice17
  · exact peakPrice18
  · exact peakPrice19
  · exact peakPrice20
  · exact peakPrice21
  · exact peakPrice22
  · exact peakPrice23
  · exact peakPrice24
  · exact peakPrice25
  · exact peakPrice26
  · exact peakPrice27
  · exact peakPrice28
  · exact peakPrice29
  · exact peakPrice30
  · exact peakPrice31
  · exact peakPrice32
  · exact peakPrice33
  · exact peakPrice34
  · exact peakPrice35
  · exact peakPrice36
  · exact peakPrice37
  · exact peakPrice38
  · exact peakPrice39
  · exact peakPrice40
  · exact peakPrice41
  · exact peakPrice42
  · exact peakPrice43
  · exact peakPrice44
  · exact peakPrice45

end

theorem proof : P0_9_8.c5 := by
  intro a ha hbox
  have hb : 1 + a.b ≤ 120 := hbox.1
  have hj : 3 + a.j ≤ 48 := hbox.2.1
  have ht : 1 + a.t ≤ 10 := hbox.2.2
  have haPos : 1 ≤ a.t := ha.1
  have haIndex : 3 * a.t ≤ a.j := ha.2.1
  have hpeak : InBox a (peak a.j) :=
    ⟨by change a.b ≤ 119; omega, le_rfl,
      le_min (by omega : a.t ≤ 9) (by omega : a.t ≤ a.j / 3)⟩
  have hpeakIndex : 3 * (peak a.j).t ≤ (peak a.j).j := by
    change 3 * min 9 (a.j / 3) ≤ a.j
    have := min_le_right 9 (a.j / 3)
    omega
  let j : Fin 43 := ⟨a.j - 3, by omega⟩
  have hj_eq : j.val + 3 = a.j := by dsimp [j]; omega
  have hprice := prices_at_cap j
  rw [hj_eq] at hprice
  exact (physical_mono hpeak haIndex hpeakIndex (oneOrder a)).trans hprice

end P0_9_8_5
end PackSource_P0_9_8_5Proof

section PackSource_P0_9_8_6Proof
set_option autoImplicit true
namespace P0_9_8_6

open K1_13_8 (availableMass fastRemaining fastRemaining_zero sum_range_truncate)
open P0_9_8 (twoStart twoOrder)
open scoped BigOperators

-- Specialize the two sums of the light K1_13_8_4Mass donor at order 84.
private def retainedTerm (k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * 2) ((k + 1) * 6)

private def tailTerm (k : ℕ) : ℕ :=
  fastRemaining (168 + (k + 1) * 2) (504 + (k + 1) * 9)

private abbrev sumTerms (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, f k

private theorem sumStep {f : ℕ → ℕ} {n total row next : ℕ}
    (hsum : sumTerms f n = total) (hrow : f n = row) (hadd : total + row = next) :
    sumTerms f (n + 1) = next := by
  unfold sumTerms at hsum ⊢
  rw [Finset.sum_range_succ, hsum, hrow, hadd]

private theorem tail_zero {k : ℕ} (hk : 127 ≤ k) : tailTerm k = 0 := by
  unfold tailTerm
  exact fastRemaining_zero (by omega)

private theorem mass_eq :
    availableMass twoStart ⟨0, 3, 0⟩ (twoOrder - 1) =
      sumTerms retainedTerm 84 + sumTerms tailTerm 127 := by
  have htrim : sumTerms tailTerm 183 = sumTerms tailTerm 127 :=
    sum_range_truncate (f := tailTerm) (fun _ hk => tail_zero hk) (by decide)
  rw [← htrim]
  simp only [availableMass, twoOrder, sumTerms, retainedTerm, tailTerm,
    show ¬ (6 : ℕ) = 0 by decide, ite_false,
    show (85 - 1 : ℕ) = 84 by decide,
    show min 84 (1650 / 6) = (84 : ℕ) by decide,
    show (6 + 3 : ℕ) = 9 by decide, show (1650 / 9 : ℕ) = 183 by decide,
    show (84 * 2 : ℕ) = 168 by decide, show (84 * 6 : ℕ) = 504 by decide,
    Nat.add_zero]

-- Each step checks one inherited symbol count and one addition on literals.
private theorem retained000 : sumTerms retainedTerm 0 = 0 := by simp
private theorem retained001 : sumTerms retainedTerm 1 = 404616625600 := sumStep retained000 (by decide : retainedTerm 0 = 404616625600) (by decide)
private theorem retained002 : sumTerms retainedTerm 2 = 804920776670 := sumStep retained001 (by decide : retainedTerm 1 = 400304151070) (by decide)
private theorem retained003 : sumTerms retainedTerm 3 = 1200942521789 := sumStep retained002 (by decide : retainedTerm 2 = 396021745119) (by decide)
private theorem retained004 : sumTerms retainedTerm 4 = 1592711834349 := sumStep retained003 (by decide : retainedTerm 3 = 391769312560) (by decide)
private theorem retained005 : sumTerms retainedTerm 5 = 1980258592447 := sumStep retained004 (by decide : retainedTerm 4 = 387546758098) (by decide)
private theorem retained006 : sumTerms retainedTerm 6 = 2363612578777 := sumStep retained005 (by decide : retainedTerm 5 = 383353986330) (by decide)
private theorem retained007 : sumTerms retainedTerm 7 = 2742803480522 := sumStep retained006 (by decide : retainedTerm 6 = 379190901745) (by decide)
private theorem retained008 : sumTerms retainedTerm 8 = 3117860889246 := sumStep retained007 (by decide : retainedTerm 7 = 375057408724) (by decide)
private theorem retained009 : sumTerms retainedTerm 9 = 3488814300786 := sumStep retained008 (by decide : retainedTerm 8 = 370953411540) (by decide)
private theorem retained010 : sumTerms retainedTerm 10 = 3855693115144 := sumStep retained009 (by decide : retainedTerm 9 = 366878814358) (by decide)
private theorem retained011 : sumTerms retainedTerm 11 = 4218526636379 := sumStep retained010 (by decide : retainedTerm 10 = 362833521235) (by decide)
private theorem retained012 : sumTerms retainedTerm 12 = 4577344072499 := sumStep retained011 (by decide : retainedTerm 11 = 358817436120) (by decide)
private theorem retained013 : sumTerms retainedTerm 13 = 4932174535353 := sumStep retained012 (by decide : retainedTerm 12 = 354830462854) (by decide)
private theorem retained014 : sumTerms retainedTerm 14 = 5283047040523 := sumStep retained013 (by decide : retainedTerm 13 = 350872505170) (by decide)
private theorem retained015 : sumTerms retainedTerm 15 = 5629990507216 := sumStep retained014 (by decide : retainedTerm 14 = 346943466693) (by decide)
private theorem retained016 : sumTerms retainedTerm 16 = 5973033758156 := sumStep retained015 (by decide : retainedTerm 15 = 343043250940) (by decide)
private theorem retained017 : sumTerms retainedTerm 17 = 6312205519476 := sumStep retained016 (by decide : retainedTerm 16 = 339171761320) (by decide)
private theorem retained018 : sumTerms retainedTerm 18 = 6647534420610 := sumStep retained017 (by decide : retainedTerm 17 = 335328901134) (by decide)
private theorem retained019 : sumTerms retainedTerm 19 = 6979048994185 := sumStep retained018 (by decide : retainedTerm 18 = 331514573575) (by decide)
private theorem retained020 : sumTerms retainedTerm 20 = 7306777675913 := sumStep retained019 (by decide : retainedTerm 19 = 327728681728) (by decide)
private theorem retained021 : sumTerms retainedTerm 21 = 7630748804483 := sumStep retained020 (by decide : retainedTerm 20 = 323971128570) (by decide)
private theorem retained022 : sumTerms retainedTerm 22 = 7950990621453 := sumStep retained021 (by decide : retainedTerm 21 = 320241816970) (by decide)
private theorem retained023 : sumTerms retainedTerm 23 = 8267531271142 := sumStep retained022 (by decide : retainedTerm 22 = 316540649689) (by decide)
private theorem retained024 : sumTerms retainedTerm 24 = 8580398800522 := sumStep retained023 (by decide : retainedTerm 23 = 312867529380) (by decide)
private theorem retained025 : sumTerms retainedTerm 25 = 8889621159110 := sumStep retained024 (by decide : retainedTerm 24 = 309222358588) (by decide)
private theorem retained026 : sumTerms retainedTerm 26 = 9195226198860 := sumStep retained025 (by decide : retainedTerm 25 = 305605039750) (by decide)
private theorem retained027 : sumTerms retainedTerm 27 = 9497241674055 := sumStep retained026 (by decide : retainedTerm 26 = 302015475195) (by decide)
private theorem retained028 : sumTerms retainedTerm 28 = 9795695241199 := sumStep retained027 (by decide : retainedTerm 27 = 298453567144) (by decide)
private theorem retained029 : sumTerms retainedTerm 29 = 10090614458909 := sumStep retained028 (by decide : retainedTerm 28 = 294919217710) (by decide)
private theorem retained030 : sumTerms retainedTerm 30 = 10382026787807 := sumStep retained029 (by decide : retainedTerm 29 = 291412328898) (by decide)
private theorem retained031 : sumTerms retainedTerm 31 = 10669959590412 := sumStep retained030 (by decide : retainedTerm 30 = 287932802605) (by decide)
private theorem retained032 : sumTerms retainedTerm 32 = 10954440131032 := sumStep retained031 (by decide : retainedTerm 31 = 284480540620) (by decide)
private theorem retained033 : sumTerms retainedTerm 33 = 11235495575656 := sumStep retained032 (by decide : retainedTerm 32 = 281055444624) (by decide)
private theorem retained034 : sumTerms retainedTerm 34 = 11513152991846 := sumStep retained033 (by decide : retainedTerm 33 = 277657416190) (by decide)
private theorem retained035 : sumTerms retainedTerm 35 = 11787439348629 := sumStep retained034 (by decide : retainedTerm 34 = 274286356783) (by decide)
private theorem retained036 : sumTerms retainedTerm 36 = 12058381516389 := sumStep retained035 (by decide : retainedTerm 35 = 270942167760) (by decide)
private theorem retained037 : sumTerms retainedTerm 37 = 12326006266759 := sumStep retained036 (by decide : retainedTerm 36 = 267624750370) (by decide)
private theorem retained038 : sumTerms retainedTerm 38 = 12590340272513 := sumStep retained037 (by decide : retainedTerm 37 = 264334005754) (by decide)
private theorem retained039 : sumTerms retainedTerm 39 = 12851410107458 := sumStep retained038 (by decide : retainedTerm 38 = 261069834945) (by decide)
private theorem retained040 : sumTerms retainedTerm 40 = 13109242246326 := sumStep retained039 (by decide : retainedTerm 39 = 257832138868) (by decide)
private theorem retained041 : sumTerms retainedTerm 41 = 13363863064666 := sumStep retained040 (by decide : retainedTerm 40 = 254620818340) (by decide)
private theorem retained042 : sumTerms retainedTerm 42 = 13615298838736 := sumStep retained041 (by decide : retainedTerm 41 = 251435774070) (by decide)
private theorem retained043 : sumTerms retainedTerm 43 = 13863575745395 := sumStep retained042 (by decide : retainedTerm 42 = 248276906659) (by decide)
private theorem retained044 : sumTerms retainedTerm 44 = 14108719861995 := sumStep retained043 (by decide : retainedTerm 43 = 245144116600) (by decide)
private theorem retained045 : sumTerms retainedTerm 45 = 14350757166273 := sumStep retained044 (by decide : retainedTerm 44 = 242037304278) (by decide)
private theorem retained046 : sumTerms retainedTerm 46 = 14589713536243 := sumStep retained045 (by decide : retainedTerm 45 = 238956369970) (by decide)
private theorem retained047 : sumTerms retainedTerm 47 = 14825614750088 := sumStep retained046 (by decide : retainedTerm 46 = 235901213845) (by decide)
private theorem retained048 : sumTerms retainedTerm 48 = 15058486486052 := sumStep retained047 (by decide : retainedTerm 47 = 232871735964) (by decide)
private theorem retained049 : sumTerms retainedTerm 49 = 15288354322332 := sumStep retained048 (by decide : retainedTerm 48 = 229867836280) (by decide)
private theorem retained050 : sumTerms retainedTerm 50 = 15515243736970 := sumStep retained049 (by decide : retainedTerm 49 = 226889414638) (by decide)
private theorem retained051 : sumTerms retainedTerm 51 = 15739180107745 := sumStep retained050 (by decide : retainedTerm 50 = 223936370775) (by decide)
private theorem retained052 : sumTerms retainedTerm 52 = 15960188712065 := sumStep retained051 (by decide : retainedTerm 51 = 221008604320) (by decide)
private theorem retained053 : sumTerms retainedTerm 53 = 16178294726859 := sumStep retained052 (by decide : retainedTerm 52 = 218106014794) (by decide)
private theorem retained054 : sumTerms retainedTerm 54 = 16393523228469 := sumStep retained053 (by decide : retainedTerm 53 = 215228501610) (by decide)
private theorem retained055 : sumTerms retainedTerm 55 = 16605899192542 := sumStep retained054 (by decide : retainedTerm 54 = 212375964073) (by decide)
private theorem retained056 : sumTerms retainedTerm 56 = 16815447493922 := sumStep retained055 (by decide : retainedTerm 55 = 209548301380) (by decide)
private theorem retained057 : sumTerms retainedTerm 57 = 17022192906542 := sumStep retained056 (by decide : retainedTerm 56 = 206745412620) (by decide)
private theorem retained058 : sumTerms retainedTerm 58 = 17226160103316 := sumStep retained057 (by decide : retainedTerm 57 = 203967196774) (by decide)
private theorem retained059 : sumTerms retainedTerm 59 = 17427373656031 := sumStep retained058 (by decide : retainedTerm 58 = 201213552715) (by decide)
private theorem retained060 : sumTerms retainedTerm 60 = 17625858035239 := sumStep retained059 (by decide : retainedTerm 59 = 198484379208) (by decide)
private theorem retained061 : sumTerms retainedTerm 61 = 17821637610149 := sumStep retained060 (by decide : retainedTerm 60 = 195779574910) (by decide)
private theorem retained062 : sumTerms retainedTerm 62 = 18014736648519 := sumStep retained061 (by decide : retainedTerm 61 = 193099038370) (by decide)
private theorem retained063 : sumTerms retainedTerm 63 = 18205179316548 := sumStep retained062 (by decide : retainedTerm 62 = 190442668029) (by decide)
private theorem retained064 : sumTerms retainedTerm 64 = 18392989678768 := sumStep retained063 (by decide : retainedTerm 63 = 187810362220) (by decide)
private theorem retained065 : sumTerms retainedTerm 65 = 18578191697936 := sumStep retained064 (by decide : retainedTerm 64 = 185202019168) (by decide)
private theorem retained066 : sumTerms retainedTerm 66 = 18760809234926 := sumStep retained065 (by decide : retainedTerm 65 = 182617536990) (by decide)
private theorem retained067 : sumTerms retainedTerm 67 = 18940866048621 := sumStep retained066 (by decide : retainedTerm 66 = 180056813695) (by decide)
private theorem retained068 : sumTerms retainedTerm 68 = 19118385795805 := sumStep retained067 (by decide : retainedTerm 67 = 177519747184) (by decide)
private theorem retained069 : sumTerms retainedTerm 69 = 19293392031055 := sumStep retained068 (by decide : retainedTerm 68 = 175006235250) (by decide)
private theorem retained070 : sumTerms retainedTerm 70 = 19465908206633 := sumStep retained069 (by decide : retainedTerm 69 = 172516175578) (by decide)
private theorem retained071 : sumTerms retainedTerm 71 = 19635957672378 := sumStep retained070 (by decide : retainedTerm 70 = 170049465745) (by decide)
private theorem retained072 : sumTerms retainedTerm 72 = 19803563675598 := sumStep retained071 (by decide : retainedTerm 71 = 167606003220) (by decide)
private theorem retained073 : sumTerms retainedTerm 73 = 19968749360962 := sumStep retained072 (by decide : retainedTerm 72 = 165185685364) (by decide)
private theorem retained074 : sumTerms retainedTerm 74 = 20131537770392 := sumStep retained073 (by decide : retainedTerm 73 = 162788409430) (by decide)
private theorem retained075 : sumTerms retainedTerm 75 = 20291951842955 := sumStep retained074 (by decide : retainedTerm 74 = 160414072563) (by decide)
private theorem retained076 : sumTerms retainedTerm 76 = 20450014414755 := sumStep retained075 (by decide : retainedTerm 75 = 158062571800) (by decide)
private theorem retained077 : sumTerms retainedTerm 77 = 20605748218825 := sumStep retained076 (by decide : retainedTerm 76 = 155733804070) (by decide)
private theorem retained078 : sumTerms retainedTerm 78 = 20759175885019 := sumStep retained077 (by decide : retainedTerm 77 = 153427666194) (by decide)
private theorem retained079 : sumTerms retainedTerm 79 = 20910319939904 := sumStep retained078 (by decide : retainedTerm 78 = 151144054885) (by decide)
private theorem retained080 : sumTerms retainedTerm 80 = 21059202806652 := sumStep retained079 (by decide : retainedTerm 79 = 148882866748) (by decide)
private theorem retained081 : sumTerms retainedTerm 81 = 21205846804932 := sumStep retained080 (by decide : retainedTerm 80 = 146643998280) (by decide)
private theorem retained082 : sumTerms retainedTerm 82 = 21350274150802 := sumStep retained081 (by decide : retainedTerm 81 = 144427345870) (by decide)
private theorem retained083 : sumTerms retainedTerm 83 = 21492506956601 := sumStep retained082 (by decide : retainedTerm 82 = 142232805799) (by decide)
private theorem retained084 : sumTerms retainedTerm 84 = 21632567230841 := sumStep retained083 (by decide : retainedTerm 83 = 140060274240) (by decide)

private theorem tail000 : sumTerms tailTerm 0 = 0 := by simp
private theorem tail001 : sumTerms tailTerm 1 = 136883723120 := sumStep tail000 (by decide : tailTerm 0 = 136883723120) (by decide)
private theorem tail002 : sumTerms tailTerm 2 = 270637894223 := sumStep tail001 (by decide : tailTerm 1 = 133754171103) (by decide)
private theorem tail003 : sumTerms tailTerm 3 = 401309204817 := sumStep tail002 (by decide : tailTerm 2 = 130671310594) (by decide)
private theorem tail004 : sumTerms tailTerm 4 = 528944041059 := sumStep tail003 (by decide : tailTerm 3 = 127634836242) (by decide)
private theorem tail005 : sumTerms tailTerm 5 = 653588479443 := sumStep tail004 (by decide : tailTerm 4 = 124644438384) (by decide)
private theorem tail006 : sumTerms tailTerm 6 = 775288289049 := sumStep tail005 (by decide : tailTerm 5 = 121699809606) (by decide)
private theorem tail007 : sumTerms tailTerm 7 = 894088927226 := sumStep tail006 (by decide : tailTerm 6 = 118800638177) (by decide)
private theorem tail008 : sumTerms tailTerm 8 = 1010035541846 := sumStep tail007 (by decide : tailTerm 7 = 115946614620) (by decide)
private theorem tail009 : sumTerms tailTerm 9 = 1123172966982 := sumStep tail008 (by decide : tailTerm 8 = 113137425136) (by decide)
private theorem tail010 : sumTerms tailTerm 10 = 1233545725167 := sumStep tail009 (by decide : tailTerm 9 = 110372758185) (by decide)
private theorem tail011 : sumTerms tailTerm 11 = 1341198023067 := sumStep tail010 (by decide : tailTerm 10 = 107652297900) (by decide)
private theorem tail012 : sumTerms tailTerm 12 = 1446173753745 := sumStep tail011 (by decide : tailTerm 11 = 104975730678) (by decide)
private theorem tail013 : sumTerms tailTerm 13 = 1548516492329 := sumStep tail012 (by decide : tailTerm 12 = 102342738584) (by decide)
private theorem tail014 : sumTerms tailTerm 14 = 1648269498281 := sumStep tail013 (by decide : tailTerm 13 = 99753005952) (by decide)
private theorem tail015 : sumTerms tailTerm 15 = 1745475711060 := sumStep tail014 (by decide : tailTerm 14 = 97206212779) (by decide)
private theorem tail016 : sumTerms tailTerm 16 = 1840177752396 := sumStep tail015 (by decide : tailTerm 15 = 94702041336) (by decide)
private theorem tail017 : sumTerms tailTerm 17 = 1932417921948 := sumStep tail016 (by decide : tailTerm 16 = 92240169552) (by decide)
private theorem tail018 : sumTerms tailTerm 18 = 2022238199583 := sumStep tail017 (by decide : tailTerm 17 = 89820277635) (by decide)
private theorem tail019 : sumTerms tailTerm 19 = 2109680241029 := sumStep tail018 (by decide : tailTerm 18 = 87442041446) (by decide)
private theorem tail020 : sumTerms tailTerm 20 = 2194785380159 := sumStep tail019 (by decide : tailTerm 19 = 85105139130) (by decide)
private theorem tail021 : sumTerms tailTerm 21 = 2277594624639 := sumStep tail020 (by decide : tailTerm 20 = 82809244480) (by decide)
private theorem tail022 : sumTerms tailTerm 22 = 2358148658217 := sumStep tail021 (by decide : tailTerm 21 = 80554033578) (by decide)
private theorem tail023 : sumTerms tailTerm 23 = 2436487836366 := sumStep tail022 (by decide : tailTerm 22 = 78339178149) (by decide)
private theorem tail024 : sumTerms tailTerm 24 = 2512652188578 := sumStep tail023 (by decide : tailTerm 23 = 76164352212) (by decide)
private theorem tail025 : sumTerms tailTerm 25 = 2586681414002 := sumStep tail024 (by decide : tailTerm 24 = 74029225424) (by decide)
private theorem tail026 : sumTerms tailTerm 26 = 2658614883743 := sumStep tail025 (by decide : tailTerm 25 = 71933469741) (by decide)
private theorem tail027 : sumTerms tailTerm 27 = 2728491636495 := sumStep tail026 (by decide : tailTerm 26 = 69876752752) (by decide)
private theorem tail028 : sumTerms tailTerm 28 = 2796350380845 := sumStep tail027 (by decide : tailTerm 27 = 67858744350) (by decide)
private theorem tail029 : sumTerms tailTerm 29 = 2862229490901 := sumStep tail028 (by decide : tailTerm 28 = 65879110056) (by decide)
private theorem tail030 : sumTerms tailTerm 30 = 2926167008601 := sumStep tail029 (by decide : tailTerm 29 = 63937517700) (by decide)
private theorem tail031 : sumTerms tailTerm 31 = 2988200639336 := sumStep tail030 (by decide : tailTerm 30 = 62033630735) (by decide)
private theorem tail032 : sumTerms tailTerm 32 = 3048367754264 := sumStep tail031 (by decide : tailTerm 31 = 60167114928) (by decide)
private theorem tail033 : sumTerms tailTerm 33 = 3106705385928 := sumStep tail032 (by decide : tailTerm 32 = 58337631664) (by decide)
private theorem tail034 : sumTerms tailTerm 34 = 3163250230575 := sumStep tail033 (by decide : tailTerm 33 = 56544844647) (by decide)
private theorem tail035 : sumTerms tailTerm 35 = 3218038643769 := sumStep tail034 (by decide : tailTerm 34 = 54788413194) (by decide)
private theorem tail036 : sumTerms tailTerm 36 = 3271106642715 := sumStep tail035 (by decide : tailTerm 35 = 53067998946) (by decide)
private theorem tail037 : sumTerms tailTerm 37 = 3322489901867 := sumStep tail036 (by decide : tailTerm 36 = 51383259152) (by decide)
private theorem tail038 : sumTerms tailTerm 38 = 3372223755257 := sumStep tail037 (by decide : tailTerm 37 = 49733853390) (by decide)
private theorem tail039 : sumTerms tailTerm 39 = 3420343192098 := sumStep tail038 (by decide : tailTerm 38 = 48119436841) (by decide)
private theorem tail040 : sumTerms tailTerm 40 = 3466882859118 := sumStep tail039 (by decide : tailTerm 39 = 46539667020) (by decide)
private theorem tail041 : sumTerms tailTerm 41 = 3511877056158 := sumStep tail040 (by decide : tailTerm 40 = 44994197040) (by decide)
private theorem tail042 : sumTerms tailTerm 42 = 3555359738511 := sumStep tail041 (by decide : tailTerm 41 = 43482682353) (by decide)
private theorem tail043 : sumTerms tailTerm 43 = 3597364512515 := sumStep tail042 (by decide : tailTerm 42 = 42004774004) (by decide)
private theorem tail044 : sumTerms tailTerm 44 = 3637924637897 := sumStep tail043 (by decide : tailTerm 43 = 40560125382) (by decide)
private theorem tail045 : sumTerms tailTerm 45 = 3677073023361 := sumStep tail044 (by decide : tailTerm 44 = 39148385464) (by decide)
private theorem tail046 : sumTerms tailTerm 46 = 3714842228937 := sumStep tail045 (by decide : tailTerm 45 = 37769205576) (by decide)
private theorem tail047 : sumTerms tailTerm 47 = 3751264461564 := sumStep tail046 (by decide : tailTerm 46 = 36422232627) (by decide)
private theorem tail048 : sumTerms tailTerm 48 = 3786371577444 := sumStep tail047 (by decide : tailTerm 47 = 35107115880) (by decide)
private theorem tail049 : sumTerms tailTerm 49 = 3820195077620 := sumStep tail048 (by decide : tailTerm 48 = 33823500176) (by decide)
private theorem tail050 : sumTerms tailTerm 50 = 3852766110335 := sumStep tail049 (by decide : tailTerm 49 = 32571032715) (by decide)
private theorem tail051 : sumTerms tailTerm 51 = 3884115466605 := sumStep tail050 (by decide : tailTerm 50 = 31349356270) (by decide)
private theorem tail052 : sumTerms tailTerm 52 = 3914273582583 := sumStep tail051 (by decide : tailTerm 51 = 30158115978) (by decide)
private theorem tail053 : sumTerms tailTerm 53 = 3943270535127 := sumStep tail052 (by decide : tailTerm 52 = 28996952544) (by decide)
private theorem tail054 : sumTerms tailTerm 54 = 3971136044169 := sumStep tail053 (by decide : tailTerm 53 = 27865509042) (by decide)
private theorem tail055 : sumTerms tailTerm 55 = 3997899468278 := sumStep tail054 (by decide : tailTerm 54 = 26763424109) (by decide)
private theorem tail056 : sumTerms tailTerm 56 = 4023589807034 := sumStep tail055 (by decide : tailTerm 55 = 25690338756) (by decide)
private theorem tail057 : sumTerms tailTerm 57 = 4048235696586 := sumStep tail056 (by decide : tailTerm 56 = 24645889552) (by decide)
private theorem tail058 : sumTerms tailTerm 58 = 4071865412031 := sumStep tail057 (by decide : tailTerm 57 = 23629715445) (by decide)
private theorem tail059 : sumTerms tailTerm 59 = 4094506862967 := sumStep tail058 (by decide : tailTerm 58 = 22641450936) (by decide)
private theorem tail060 : sumTerms tailTerm 60 = 4116187595877 := sumStep tail059 (by decide : tailTerm 59 = 21680732910) (by decide)
private theorem tail061 : sumTerms tailTerm 61 = 4136934789677 := sumStep tail060 (by decide : tailTerm 60 = 20747193800) (by decide)
private theorem tail062 : sumTerms tailTerm 62 = 4156775258105 := sumStep tail061 (by decide : tailTerm 61 = 19840468428) (by decide)
private theorem tail063 : sumTerms tailTerm 63 = 4175735445264 := sumStep tail062 (by decide : tailTerm 62 = 18960187159) (by decide)
private theorem tail064 : sumTerms tailTerm 64 = 4193841428016 := sumStep tail063 (by decide : tailTerm 63 = 18105982752) (by decide)
private theorem tail065 : sumTerms tailTerm 65 = 4211118911520 := sumStep tail064 (by decide : tailTerm 64 = 17277483504) (by decide)
private theorem tail066 : sumTerms tailTerm 66 = 4227593231631 := sumStep tail065 (by decide : tailTerm 65 = 16474320111) (by decide)
private theorem tail067 : sumTerms tailTerm 67 = 4243289350433 := sumStep tail066 (by decide : tailTerm 66 = 15696118802) (by decide)
private theorem tail068 : sumTerms tailTerm 68 = 4258231858643 := sumStep tail067 (by decide : tailTerm 67 = 14942508210) (by decide)
private theorem tail069 : sumTerms tailTerm 69 = 4272444971139 := sumStep tail068 (by decide : tailTerm 68 = 14213112496) (by decide)
private theorem tail070 : sumTerms tailTerm 70 = 4285952529369 := sumStep tail069 (by decide : tailTerm 69 = 13507558230) (by decide)
private theorem tail071 : sumTerms tailTerm 71 = 4298777996874 := sumStep tail070 (by decide : tailTerm 70 = 12825467505) (by decide)
private theorem tail072 : sumTerms tailTerm 72 = 4310944461702 := sumStep tail071 (by decide : tailTerm 71 = 12166464828) (by decide)
private theorem tail073 : sumTerms tailTerm 73 = 4322474631926 := sumStep tail072 (by decide : tailTerm 72 = 11530170224) (by decide)
private theorem tail074 : sumTerms tailTerm 74 = 4333390838063 := sumStep tail073 (by decide : tailTerm 73 = 10916206137) (by decide)
private theorem tail075 : sumTerms tailTerm 75 = 4343715028587 := sumStep tail074 (by decide : tailTerm 74 = 10324190524) (by decide)
private theorem tail076 : sumTerms tailTerm 76 = 4353468772353 := sumStep tail075 (by decide : tailTerm 75 = 9753743766) (by decide)
private theorem tail077 : sumTerms tailTerm 77 = 4362673254105 := sumStep tail076 (by decide : tailTerm 76 = 9204481752) (by decide)
private theorem tail078 : sumTerms tailTerm 78 = 4371349276905 := sumStep tail077 (by decide : tailTerm 77 = 8676022800) (by decide)
private theorem tail079 : sumTerms tailTerm 79 = 4379517257636 := sumStep tail078 (by decide : tailTerm 78 = 8167980731) (by decide)
private theorem tail080 : sumTerms tailTerm 80 = 4387197229436 := sumStep tail079 (by decide : tailTerm 79 = 7679971800) (by decide)
private theorem tail081 : sumTerms tailTerm 81 = 4394408837196 := sumStep tail080 (by decide : tailTerm 80 = 7211607760) (by decide)
private theorem tail082 : sumTerms tailTerm 82 = 4401171339999 := sumStep tail081 (by decide : tailTerm 81 = 6762502803) (by decide)
private theorem tail083 : sumTerms tailTerm 83 = 4407503606613 := sumStep tail082 (by decide : tailTerm 82 = 6332266614) (by decide)
private theorem tail084 : sumTerms tailTerm 84 = 4413424117935 := sumStep tail083 (by decide : tailTerm 83 = 5920511322) (by decide)
private theorem tail085 : sumTerms tailTerm 85 = 4418950962479 := sumStep tail084 (by decide : tailTerm 84 = 5526844544) (by decide)
private theorem tail086 : sumTerms tailTerm 86 = 4424101838825 := sumStep tail085 (by decide : tailTerm 85 = 5150876346) (by decide)
private theorem tail087 : sumTerms tailTerm 87 = 4428894051102 := sumStep tail086 (by decide : tailTerm 86 = 4792212277) (by decide)
private theorem tail088 : sumTerms tailTerm 88 = 4433344511442 := sumStep tail087 (by decide : tailTerm 87 = 4450460340) (by decide)
private theorem tail089 : sumTerms tailTerm 89 = 4437469735458 := sumStep tail088 (by decide : tailTerm 88 = 4125224016) (by decide)
private theorem tail090 : sumTerms tailTerm 90 = 4441285844703 := sumStep tail089 (by decide : tailTerm 89 = 3816109245) (by decide)
private theorem tail091 : sumTerms tailTerm 91 = 4444808562143 := sumStep tail090 (by decide : tailTerm 90 = 3522717440) (by decide)
private theorem tail092 : sumTerms tailTerm 92 = 4448053214621 := sumStep tail091 (by decide : tailTerm 91 = 3244652478) (by decide)
private theorem tail093 : sumTerms tailTerm 93 = 4451034728325 := sumStep tail092 (by decide : tailTerm 92 = 2981513704) (by decide)
private theorem tail094 : sumTerms tailTerm 94 = 4453767631257 := sumStep tail093 (by decide : tailTerm 93 = 2732902932) (by decide)
private theorem tail095 : sumTerms tailTerm 95 = 4456266048696 := sumStep tail094 (by decide : tailTerm 94 = 2498417439) (by decide)
private theorem tail096 : sumTerms tailTerm 96 = 4458543705672 := sumStep tail095 (by decide : tailTerm 95 = 2277656976) (by decide)
private theorem tail097 : sumTerms tailTerm 97 = 4460613922424 := sumStep tail096 (by decide : tailTerm 96 = 2070216752) (by decide)
private theorem tail098 : sumTerms tailTerm 98 = 4462489616879 := sumStep tail097 (by decide : tailTerm 97 = 1875694455) (by decide)
private theorem tail099 : sumTerms tailTerm 99 = 4464183300105 := sumStep tail098 (by decide : tailTerm 98 = 1693683226) (by decide)
private theorem tail100 : sumTerms tailTerm 100 = 4465707078795 := sumStep tail099 (by decide : tailTerm 99 = 1523778690) (by decide)
private theorem tail101 : sumTerms tailTerm 101 = 4467072650715 := sumStep tail100 (by decide : tailTerm 100 = 1365571920) (by decide)
private theorem tail102 : sumTerms tailTerm 102 = 4468291307193 := sumStep tail101 (by decide : tailTerm 101 = 1218656478) (by decide)
private theorem tail103 : sumTerms tailTerm 103 = 4469373928562 := sumStep tail102 (by decide : tailTerm 102 = 1082621369) (by decide)
private theorem tail104 : sumTerms tailTerm 104 = 4470330986654 := sumStep tail103 (by decide : tailTerm 103 = 957058092) (by decide)
private theorem tail105 : sumTerms tailTerm 105 = 4471172540238 := sumStep tail104 (by decide : tailTerm 104 = 841553584) (by decide)
private theorem tail106 : sumTerms tailTerm 106 = 4471908237519 := sumStep tail105 (by decide : tailTerm 105 = 735697281) (by decide)
private theorem tail107 : sumTerms tailTerm 107 = 4472547311571 := sumStep tail106 (by decide : tailTerm 106 = 639074052) (by decide)
private theorem tail108 : sumTerms tailTerm 108 = 4473098582841 := sumStep tail107 (by decide : tailTerm 107 = 551271270) (by decide)
private theorem tail109 : sumTerms tailTerm 109 = 4473570454577 := sumStep tail108 (by decide : tailTerm 108 = 471871736) (by decide)
private theorem tail110 : sumTerms tailTerm 110 = 4473970915337 := sumStep tail109 (by decide : tailTerm 109 = 400460760) (by decide)
private theorem tail111 : sumTerms tailTerm 111 = 4474307534412 := sumStep tail110 (by decide : tailTerm 110 = 336619075) (by decide)
private theorem tail112 : sumTerms tailTerm 112 = 4474587464340 := sumStep tail111 (by decide : tailTerm 111 = 279929928) (by decide)
private theorem tail113 : sumTerms tailTerm 113 = 4474817436324 := sumStep tail112 (by decide : tailTerm 112 = 229971984) (by decide)
private theorem tail114 : sumTerms tailTerm 114 = 4475003762751 := sumStep tail113 (by decide : tailTerm 113 = 186326427) (by decide)
private theorem tail115 : sumTerms tailTerm 115 = 4475152332605 := sumStep tail114 (by decide : tailTerm 114 = 148569854) (by decide)
private theorem tail116 : sumTerms tailTerm 116 = 4475268613991 := sumStep tail115 (by decide : tailTerm 115 = 116281386) (by decide)
private theorem tail117 : sumTerms tailTerm 117 = 4475357649543 := sumStep tail116 (by decide : tailTerm 116 = 89035552) (by decide)
private theorem tail118 : sumTerms tailTerm 118 = 4475424058953 := sumStep tail117 (by decide : tailTerm 117 = 66409410) (by decide)
private theorem tail119 : sumTerms tailTerm 119 = 4475472034374 := sumStep tail118 (by decide : tailTerm 118 = 47975421) (by decide)
private theorem tail120 : sumTerms tailTerm 120 = 4475505342954 := sumStep tail119 (by decide : tailTerm 119 = 33308580) (by decide)
private theorem tail121 : sumTerms tailTerm 121 = 4475527322234 := sumStep tail120 (by decide : tailTerm 120 = 21979280) (by decide)
private theorem tail122 : sumTerms tailTerm 122 = 4475540882687 := sumStep tail121 (by decide : tailTerm 121 = 13560453) (by decide)
private theorem tail123 : sumTerms tailTerm 123 = 4475548503111 := sumStep tail122 (by decide : tailTerm 122 = 7620424) (by decide)
private theorem tail124 : sumTerms tailTerm 124 = 4475552233173 := sumStep tail123 (by decide : tailTerm 123 = 3730062) (by decide)
private theorem tail125 : sumTerms tailTerm 125 = 4475553688797 := sumStep tail124 (by decide : tailTerm 124 = 1455624) (by decide)
private theorem tail126 : sumTerms tailTerm 126 = 4475554054713 := sumStep tail125 (by decide : tailTerm 125 = 365916) (by decide)
private theorem tail127 : sumTerms tailTerm 127 = 4475554079840 := sumStep tail126 (by decide : tailTerm 126 = 25127) (by decide)

theorem proof : P0_9_8.c6 := by
  unfold P0_9_8.c6
  rw [mass_eq, retained084, tail127]
  decide

end P0_9_8_6
end PackSource_P0_9_8_6Proof

section PackSource_P0_9_8_7Aux
set_option autoImplicit true
namespace P0_9_8_7

open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)

private theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩

private theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩

private theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩

private theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩

private theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩

private theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩

private theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩

private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega

private theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
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
    P0_9.surfaceNumerator32 p q ≤ P0_9.surfaceNumerator32 p' q := by
  let L := P0_9.taylorLength
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

private theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)

/-- Physical tariffs increase with the factor shape within the index chamber. -/
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : P0_9.physicalPrice x l ≤ P0_9.physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := P0_9.primaryBox
  let L := P0_9.taylorLength
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
  have hmain : (P0.t + 2*P0_9.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P0.t + 2*P0_9.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P0.t hc) (Nat.mul_le_mul_left (2*P0_9.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*P0_9.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)

end P0_9_8_7
end PackSource_P0_9_8_7Aux

section PackSource_P0_9_8_7Proof
set_option autoImplicit true
namespace P0_9_8_7

open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8 (fullCap)
open P0_9_8 (twoStart twoOrder factorCap twoReserve indexBudget)

private def budget (j : ℕ) : ℕ := indexBudget twoStart (factorCap - twoReserve) j

private def peak (j : ℕ) : Shape := ⟨118, j, min 8 (j / 3)⟩

private theorem ceil_le {a b k : ℕ} (h : a ≤ b) : ceilDiv a k ≤ ceilDiv b k :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h k) 1)

/-- The three lifted terms and the four auxiliary terms, all in units of 1/32. -/
private def priceFromParts (f m₀ m₁ m₂ c₀ c₁ p₀ p₁ : ℕ) : ℕ :=
  ceilDiv (ceilDiv (m₀ + 133553 * m₁ + 133554 * m₂) 32 +
    ceilDiv ((81936 + 2 * 46657) * 118 * 4012 * 31251403) 46657) 85 +
  2 * 133551 * 118 * 4012 +
  ceilDiv (81936 * (c₀ + 2 * f * c₁) + 93314 * (p₀ + 2 * f * p₁)) 1493024

/-- A single row uses the lifted upper bound on the minimum in the surface term. -/
private theorem row_le (j f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance : ℕ) :
    let a : Shape := ⟨118, j, f⟩
    let p := a.chamber
    let q := P0_9.primaryBox
    let L := P0_9.taylorLength
    let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
    let e₁ := liftedChart (L + 1) p
    let e₂ := liftedChart (L + 2) p
    let h := chart L p
    let z := q.plus (p.scale 4)
    mixed32 p q e₁ e₂ = m₀ → mixed32 p q g e₂ = m₁ → mixed32 p q g e₁ = m₂ →
    mixed32 p q z h = c₀ → mixed32 p p p h = c₁ →
    mixed32 p q z p = p₀ → mixed32 p p p p = p₁ →
    (chart (L + 1) p).b = 31251403 →
    priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ = price → budget j = allowance →
    price ≤ allowance → P0_9.physicalPrice a twoOrder ≤ budget j := by
  intro a p q L g e₁ e₂ h z hm₀ hm₁ hm₂ hc₀ hc₁ hp₀ hp₁ hb hprice hbudget hle
  have hsurface : P0_9.surfaceNumerator32 p q ≤ m₀ + 133553 * m₁ + 133554 * m₂ := by
    unfold P0_9.surfaceNumerator32
    change min _ (mixed32 p q e₁ e₂ + 133553 * mixed32 p q g e₂ +
      133554 * mixed32 p q g e₁) ≤ _
    rw [hm₀, hm₁, hm₂]
    exact min_le_right _ _
  have hpaid : P0_9.physicalPrice a twoOrder ≤ priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ := by
    unfold P0_9.physicalPrice priceFromParts
    change ceilDiv (ceilDiv (P0_9.surfaceNumerator32 p q) 32 +
          ceilDiv ((81936 + 2 * 46657) * 118 * 4012 * (chart (L + 1) p).b) 46657) 85 +
        2 * 133551 * 118 * 4012 +
        ceilDiv (81936 * (mixed32 p q z h + 2 * f * mixed32 p p p h) +
          93314 * (mixed32 p q z p + 2 * f * mixed32 p p p p)) 1493024 ≤ _
    rw [hb, hc₀, hc₁, hp₀, hp₁]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (ceil_le (Nat.add_le_add_right (ceil_le hsurface) _)) _) _
  rw [← hprice] at hle
  rw [hbudget]
  exact hpaid.trans hle

section

set_option maxRecDepth 4096

-- Each row certifies seven individual mixed terms before comparing literal prices.
private theorem row3 : P0_9.physicalPrice (peak 3) twoOrder ≤ budget 3 :=
  row_le 3 1 128984903463054752 2629231032704 2629211345536
    1621008534421920 6734276376 10788796512 67176 395354681588713 8391438548505418
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row4 : P0_9.physicalPrice (peak 4) twoOrder ≤ budget 4 :=
  row_le 4 1 369399110372512000 5274390133760 5274350603072
    2603091937137664 22353488640 14611385728 156120 797396753778043 11188584731340557
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row5 : P0_9.physicalPrice (peak 5) twoOrder ≤ budget 5 :=
  row_le 5 1 721808127785121632 8764728564320 8764662935360
    3615341595707104 48229505256 18546941152 288744 1325267257458474 13985730914175697
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row6 : P0_9.physicalPrice (peak 6) twoOrder ≤ budget 6 :=
  row_le 6 2 1186775262716288000 13104464336000 13104366211648
    4658027981777472 97567947840 22597140096 531072 1979614498989100 16782877097010836
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row7 : P0_9.physicalPrice (peak 7) twoOrder ≤ budget 7 :=
  row_le 7 2 1764863822181193888 18297815460416 18297678411968
    5730948113403424 164169866616 26760336352 837504 2761033860607292 19580023279845976
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row8 : P0_9.physicalPrice (peak 8) twoOrder ≤ budget 8 :=
  row_le 8 2 2456637113195132864 24348999949184 24348817627136
    6834135735435904 252214904832 31036877824 1229184 3670154720814581 22377169462681115
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row9 : P0_9.physicalPrice (peak 9) twoOrder ≤ budget 9 :=
  row_le 9 3 3262658442773509280 31262235813920 31262001726400
    7967861319522144 374639443272 35428441824 1770984 4707657187396531 25174315645516255
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row10 : P0_9.physicalPrice (peak 10) twoOrder ≤ budget 10 :=
  row_le 10 3 4183491117931505920 39041741066240 39041448689792
    9131921883716800 525141964224 39933382144 2417112 5874084326339043 27971461828351394
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row11 : P0_9.physicalPrice (peak 11) twoOrder ≤ budget 11 :=
  row_le 11 3 5219698445684416352 47691733717760 47691376608128
    10326351172870816 707709796056 44552046688 3187944 7170088300811448 30768608011186534
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row12 : P0_9.physicalPrice (peak 12) twoOrder ≤ budget 12 :=
  row_le 12 4 6371843733047644928 57216431780096 57216003350656
    11551419658631424 935010078720 49286112768 4147200 8596412055539098 33565754194021673
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row13 : P0_9.physicalPrice (peak 13) twoOrder ≤ budget 13 :=
  row_le 13 4 7640490287036374432 67620053264864 67619546897408
    12806924359053280 1200638726568 54133934176 5248896 10153487555787616 36362900376856813
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row14 : P0_9.physicalPrice (peak 14) twoOrder ≤ budget 14 :=
  row_le 14 4 9026201414665898432 78906816183680 78906225339200
    14092899018987328 1508390753088 59095858816 6512640 11842017312596815 39160046559691952
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row15 : P0_9.physicalPrice (peak 15) twoOrder ≤ budget 15 :=
  row_le 15 5 10529540422951621280 91080938548160 91080256545280
    15409614110080800 1870664057400 64173564000 8001000 13662848239231388 41957192742527092
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row16 : P0_9.physicalPrice (peak 16) twoOrder ≤ budget 16 :=
  row_le 16 5 12151070618908725760 104146638369920 104145858495680
    16756866650388352 2280951985920 69365403520 9667800 15616222037842609 44754338925362231
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row17 : P0_9.physicalPrice (peak 17) twoOrder ≤ budget 17 :=
  row_le 17 5 13891355309552505440 118108133660576 118107249281216
    18134690384760928 2742857237256 74671725280 11531880 17702929412382493 47551485108197371
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row18 : P0_9.physicalPrice (peak 18) twoOrder ≤ budget 18 :=
  row_le 18 6 15750957801898364672 132969642431744 132968646771136
    19543355784845760 3268508469696 80094206592 13654656 19923971915082431 50348631291032510
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row19 : P0_9.physicalPrice (peak 19) twoOrder ≤ budget 19 :=
  row_le 19 6 17730441402961486240 148735382695040 148734268945472
    20982659868697504 3851296461720 85631201248 15989760 22279302559176849 53145777473867650
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row20 : P0_9.physicalPrice (peak 20) twoOrder ≤ budget 20 :=
  row_le 20 6 19830369419757163712 165409572462080 165408333895040
    22452636381167104 4494631597056 91283057152 18555264 24769847811152299 55942923656702789
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row21 : P0_9.physicalPrice (peak 21) twoOrder ≤ budget 21 :=
  row_le 21 7 22051305159300801440 182996429744480 182995059489088
    23953555793901792 5210373293160 97051451616 21411432 27396823514203641 58740069839537929
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row22 : P0_9.physicalPrice (peak 22) twoOrder ≤ budget 22 :=
  row_le 22 7 24393811928607582208 201500172553856 201498663707648
    25485215124956224 5991809760576 102934738432 24511704 30159777417954335 61537216022373068
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row23 : P0_9.physicalPrice (peak 23) twoOrder ≤ budget 23 :=
  row_le 23 7 26858453034692799584 220925018901824 220923364641536
    27047648119181344 6842159068152 108933265504 27873384 33059828488370012 64334362205208207
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row24 : P0_9.physicalPrice (peak 24) twoOrder ≤ budget 24 :=
  row_le 24 8 29445791784571857920 241275186800000 241273380160000
    28641125248224384 7773011392512 115048710144 31555584 36098474935916766 67131508388043347
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row25 : P0_9.physicalPrice (peak 25) twoOrder ≤ budget 25 :=
  row_le 25 8 32156391485259940000 262554894260000 262552928243072
    30265443530140000 8777552376264 121279426144 35511552 39274725637538183 69928654570878486
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row26 : P0_9.physicalPrice (peak 26) twoOrder ≤ budget 26 :=
  row_le 26 8 34990815443772339392 284768359293440 284766226981568
    31920636709779136 9858807773376 127625761408 39757824 42589957405687315 72725800753713626
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row27 : P0_9.physicalPrice (peak 27) twoOrder ≤ budget 27 :=
  row_le 27 8 37948639069213326944 307912402476512 307910096864704
    33606620168594592 11015565999960 134087399136 44289792 46043696205897641 75522946936548765
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row28 : P0_9.physicalPrice (peak 28) twoOrder ≤ budget 28 :=
  row_le 28 8 41028120494566129408 331973980842752 331971495060608
    35323309288039168 12246615472128 140664022528 49102848 49634015111122505 78320093119383905
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row29 : P0_9.physicalPrice (peak 29) twoOrder ≤ budget 29 :=
  row_le 29 8 44227847171843957600 356942517311360 356939844567680
    37070619449565664 13550744605992 147355314784 54192384 53359350417460185 81117239302219044
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row30 : P0_9.physicalPrice (peak 30) twoOrder ≤ budget 30 :=
  row_le 30 8 47546406553060133120 382807434801536 382804568384320
    38848466034626880 14926741817664 154160959104 59553792 57218138421008996 83914385485054184
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row31 : P0_9.physicalPrice (peak 31) twoOrder ≤ budget 31 :=
  row_le 31 8 50982386090227977568 409558156232480 409555089508928
    40656764424675616 16373395523256 161080638688 65182464 61208815417867256 86711531667889323
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row32 : P0_9.physicalPrice (peak 32) twoOrder ≤ budget 32 :=
  row_le 32 8 54534373235360812544 437184104523392 437180830939904
    42495430001164672 17889494138880 168114036736 71073792 65329817704133282 89508677850724463
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row33 : P0_9.physicalPrice (peak 33) twoOrder ≤ budget 33 :=
  row_le 33 8 58200955440471959648 465674702593472 465671215675648
    44364378145546848 19473826080648 175260836448 77223168 69579581575905391 92305824033559602
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row34 : P0_9.physicalPrice (peak 34) twoOrder ≤ budget 34 :=
  row_le 34 8 61980720157574740480 495019373361920 495015666714560
    46263524239274944 21125179764672 182520721024 83625984 73956543329281900 95102970216394742
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row35 : P0_9.physicalPrice (peak 35) twoOrder ≤ budget 35 :=
  row_le 35 8 65872254838682476640 525207539747936 525203607055040
    48192783663801760 22842343607064 189893373664 90277632 78459139260361125 97900116399229881
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row36 : P0_9.physicalPrice (peak 36) twoOrder ≤ budget 36 :=
  row_le 36 8 69874146935808489728 556228624670720 556224459695488
    50152071800580096 24624106023936 197378477568 97173504 83085805665241386 100697262582065021
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row37 : P0_9.physicalPrice (peak 37) twoOrder ≤ budget 37 :=
  row_le 37 8 73984983900966101344 588072051049472 588067647634304
    52141304031062752 26469255431400 204975715936 104308992 87834978840020995 103494408764900160
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row38 : P0_9.physicalPrice (peak 38) twoOrder ≤ budget 38 :=
  row_le 38 8 78203353186168633088 620727241803392 620722593869888
    54160395736702528 28376580245568 212684771968 111679488 92705095080798275 106291554947735300
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row39 : P0_9.physicalPrice (peak 39) twoOrder ≤ budget 39 :=
  row_le 39 8 82527842243429406560 654183619851680 654178721400640
    56209262298952224 30344868882552 220505328864 119280384 97694590683671539 109088701130570439
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row40 : P0_9.physicalPrice (peak 40) twoOrder ≤ budget 40 :=
  row_le 40 8 86957038524761743360 688430608113536 688425453224960
    58287819099264640 32372909758464 228437069824 127107072 102801901944739104 111885847313405579
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row41 : P0_9.physicalPrice (peak 41) twoOrder ≤ budget 41 :=
  row_le 41 8 91489529482178965088 723457629508160 723452212341248
    60395981519092576 34459491289416 236479678048 135154944 108025465160099289 114682993496240718
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem row42 : P0_9.physicalPrice (peak 42) twoOrder ≤ budget 42 :=
  row_le 42 8 96123902567694393344 759254106954752 759248421747904
    62533664939888832 36603401891520 244632836736 143419392 113363716625850410 117480139679075858
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)

private theorem peak_bound (i : Fin 40) :
    P0_9.physicalPrice (peak (i.val + 3)) twoOrder ≤ budget (i.val + 3) := by
  fin_cases i
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42

end

theorem proof : P0_9_8.c7 := by
  intro a ha hbox
  change 2 + a.b ≤ 120 ∧ 6 + a.j ≤ 48 ∧ 2 + a.t ≤ 10 at hbox
  obtain ⟨hb, hj, ht⟩ := hbox
  have hlo : 3 ≤ a.j := (Nat.mul_le_mul_left 3 ha.1).trans ha.2.1
  have hfit : 3 * a.t ≤ a.j := ha.2.1
  have hpeak : InBox a (peak a.j) :=
    ⟨by change a.b ≤ 118; omega, le_rfl, by change a.t ≤ min 8 (a.j / 3); omega⟩
  have hpeakFit : 3 * (peak a.j).t ≤ a.j := by
    change 3 * min 8 (a.j / 3) ≤ a.j
    have h := min_le_right 8 (a.j / 3)
    omega
  let i : Fin 40 := ⟨a.j - 3, by omega⟩
  have hi : i.val + 3 = a.j := by change a.j - 3 + 3 = a.j; omega
  have hrow := peak_bound i
  rw [hi] at hrow
  exact (physical_mono hpeak hfit hpeakFit twoOrder).trans hrow

end P0_9_8_7
end PackSource_P0_9_8_7Proof

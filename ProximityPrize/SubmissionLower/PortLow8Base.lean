import ProximityPrize.SubmissionLower.Low27Definitions
import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
section PackSource_P0_9_8Defs
set_option autoImplicit true
namespace P0_9_8

open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape fullCap availableMass)
open K1_13_8_2 (Threshold orderFor)

abbrev factorCap : ℕ := 222671385202463816
abbrev oneReserve : ℕ := 39000000000000000
abbrev twoReserve : ℕ := 111000000000000000

abbrev oneStart : Shape := ⟨1, 3, 1⟩
abbrev twoStart : Shape := ⟨2, 6, 2⟩

/-- Each empty-start threshold supplies an order on the quadrant above it. -/
def emptyThresholds : List Threshold :=
  [⟨107,46,55⟩, ⟨14,41,53⟩, ⟨61,31,51⟩, ⟨8,13,31⟩, ⟨9,7,9⟩, ⟨22,4,8⟩, ⟨3,7,4⟩, ⟨109,10,50⟩, ⟨98,11,49⟩, ⟨88,12,48⟩, ⟨7,20,42⟩, ⟨119,48,56⟩, ⟨107,10,50⟩, ⟨96,11,49⟩, ⟨87,12,48⟩, ⟨118,48,56⟩]

def emptyOrder (x : Shape) : ℕ := orderFor x.b x.j emptyThresholds

/-- For a retained factor of top degree one, use only the positive index spend. -/
def oneOrder (x : Shape) : ℕ := if x.j ≤ 3 then 1 else if x.j = 4 then 3 else (3 * x.j - 4) / 2

def twoOrder (a : Shape) : ℕ :=
  if a.j < 4 then 68 else if a.j < 5 then 72 else if a.j < 6 then 84 else if a.j < 42 then 85 else 90

def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (48 - r.j)

def edgePrice (a : Shape) (L : ℕ) : ℕ :=
  if FatEligible a then min (P0_9.physicalPrice a L) (P0_9.fatPrice a)
  else P0_9.physicalPrice a L

/-- The positive phase uses a reverse potential. Every intermediate state may stop. -/
def Bellman (r : Shape) (cap tcap : ℕ) : Prop :=
  ∃ (B order : Shape → ℕ), B zeroShape ≤ cap ∧
    (∀ x, Valid x → InBox (r.plus x) fullCap →
      0 < order x ∧
        (order x = 1 ∨ availableMass r x (order x - 1) < P0_9.layerNeed)) ∧
    (∀ (y a : Shape), (y = zeroShape ∨ Valid y) → Valid a → a.t ≤ tcap →
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
  split_ifs <;> omega

theorem oneOrder_mono {x y : Shape} (h : x.j ≤ y.j) : oneOrder x ≤ oneOrder y := by
  unfold oneOrder
  split_ifs <;> omega

/-- An index-linear potential turns single-factor charges into a prefix bound. -/
theorem bellman_of_budget (r : Shape) (cap tcap : ℕ) (order : Shape → ℕ)
    (hpos : ∀ x, 0 < order x)
    (hmono : ∀ {a x}, a.b ≤ x.b → a.j ≤ x.j → order a ≤ order x)
    (horders : ∀ x, Valid x → InBox (r.plus x) fullCap →
      order x = 1 ∨ availableMass r x (order x - 1) < P0_9.layerNeed)
    (hprice : ∀ a, Valid a → a.t ≤ tcap → InBox (r.plus a) fullCap →
      P0_9.physicalPrice a (order a) ≤ indexBudget r cap a.j) :
    Bellman r cap tcap := by
  let B := fun y : Shape => indexBudget r cap (48 - r.j - y.j)
  refine ⟨B, order, ?_, fun x hx hb => ⟨hpos x, horders x hx hb⟩, ?_⟩
  · change cap * (48 - r.j - 0) / (48 - r.j) ≤ cap
    rw [Nat.sub_zero]
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm])
  · intro y a _ ha ht hbox
    let x := y.plus a
    have hb : InBox (r.plus a) fullCap :=
      ⟨(Nat.add_le_add_left (Nat.le_add_left a.b y.b) _).trans hbox.1,
        (Nat.add_le_add_left (Nat.le_add_left a.j y.j) _).trans hbox.2.1,
        (Nat.add_le_add_left (Nat.le_add_left a.t y.t) _).trans hbox.2.2⟩
    have hl := hmono (a := a) (x := x) (Nat.le_add_left _ _) (Nat.le_add_left _ _)
    have hfee := (edgePrice_anti a (hpos a) hl).trans
      ((edgePrice_le_physical a _).trans (hprice a ha ht hb))
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
open K1_13_8 (Valid zeroShape fullCap availableMass layerTerm layerCount)
open K1_13_8_2 (Threshold orderFor)
open scoped BigOperators

open K1_13
open K1_13_8 (zeroMass zeroMass_upper remaining_anti fastRemaining)

def RetainedBox27 (a : Shape) : Prop :=
  a.b ≤ 20 ∧ a.j ≤ 6 ∧ (4 ≤ a.j → a.b ≤ 17) ∧ (5 ≤ a.j → a.b ≤ 14) ∧ (6 ≤ a.j → a.b ≤ 7)

def loopSum (f : ℕ → ℕ) : ℕ → ℕ | 0 => 0 | n+1 => loopSum f n + f n
theorem sum_eq (f : ℕ → ℕ) (n : ℕ) : ∑ k ∈ Finset.range n, f k = loopSum f n := by
  induction n with
  | zero => simp [loopSum]
  | succ n ih => rw [Finset.sum_range_succ, ih, loopSum]
private theorem retained_bound (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r : Shape} (hr : Valid r)
    (hmass : P0_9.layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      remaining ((k + 1) * r.b) ((k + 1) * r.j)) : RetainedBox27 r := by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall : zeroMass b j < P0_9.layerNeed) : False := by
    have hle : P0_9.layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (zeroMass_upper hcount hjpos)
    omega
  obtain ⟨ht, hjt, hjb⟩ := hr
  have h20 : zeroMass 21 3 < P0_9.layerNeed := by unfold zeroMass; rw [sum_eq]; decide +kernel
  have h18 : zeroMass 18 4 < P0_9.layerNeed := by unfold zeroMass; rw [sum_eq]; decide +kernel
  have h14 : zeroMass 15 5 < P0_9.layerNeed := by unfold zeroMass; rw [sum_eq]; decide +kernel
  have h7 : zeroMass 8 6 < P0_9.layerNeed := by unfold zeroMass; rw [sum_eq]; decide +kernel
  have hj7 : zeroMass 3 7 < P0_9.layerNeed := by unfold zeroMass; rw [sum_eq]; decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) h20
  · by_contra! h; exact reject (by omega) (by omega) (by decide) hj7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h18
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h14
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h7

private theorem retainedBox_down {a r : Shape} (h : InBox a r) (hr : RetainedBox27 r) : RetainedBox27 a := by
  rcases h with ⟨hb, hj, _⟩
  rcases hr with ⟨hrb, hrj, h4, h5, h6⟩
  exact ⟨hb.trans hrb, hj.trans hrj, fun k => hb.trans (h4 (k.trans hj)),
    fun k => hb.trans (h5 (k.trans hj)), fun k => hb.trans (h6 (k.trans hj))⟩

/-- Fat fees within the enclosing box of feasible retained products. -/
def c1 : Prop :=
  ∀ a, Valid a → RetainedBox27 a →
    P0_9.fatPrice a ≤ (if a.t = 1 then oneReserve else 55500000000000000) * a.t

/-- Seven evaluations certify the order when nothing has been retained. -/
def c2 : Prop :=
  ∀ s ∈ emptyThresholds,
    availableMass zeroShape ⟨s.b, s.j, 0⟩ (s.l - 1) < P0_9.layerNeed

/-- A single positive fee uses at most its share of the total index budget. -/
def c3 : Prop :=
  ∀ a tcap, Valid a → a.t ≤ tcap → InBox (zeroShape.plus a) fullCap →
    P0_9.physicalPrice a (emptyOrder a) ≤ indexBudget zeroShape (P0_9.factorPrice tcap) a.j

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
  ∀ j : ℕ, 3 ≤ j → j ≤ 42 → availableMass twoStart ⟨0, j, 0⟩ (twoOrder ⟨0,j,0⟩ - 1) < P0_9.layerNeed

/-- The paid index budget for two units of retained top degree. -/
def c7 : Prop :=
  ∀ a, Valid a → InBox (twoStart.plus a) fullCap →
    P0_9.physicalPrice a (twoOrder a) ≤ indexBudget twoStart (factorCap - twoReserve) a.j

private theorem empty_bellman (tcap : ℕ) (horder : c2) (hprice : c3) :
    Bellman zeroShape (P0_9.factorPrice tcap) tcap := by
  apply bellman_of_budget zeroShape (P0_9.factorPrice tcap) tcap emptyOrder
    (fun x => (orderFor_select x.b x.j emptyThresholds).1)
    (fun hb hj => orderFor_mono hb hj emptyThresholds) _ (fun a ha ht hb => hprice a tcap ha ht hb)
  intro x _ _
  rcases (orderFor_select x.b x.j emptyThresholds).2 with he | ⟨s, hs, hb, hj, he⟩
  · exact Or.inl he
  · have hj0 : 0 < s.j := by
      simp [emptyThresholds] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    right
    change emptyOrder x = s.l at he
    rw [he]
    exact (availableMass_anti_prefix (y := ⟨s.b, s.j, 0⟩)
      (Or.inl rfl) (by simpa [zeroShape] using hj0) hb hj).trans_lt (horder s hs)

private theorem one_bellman (tcap : ℕ) (horder : c4) (hprice : c5) :
    Bellman oneStart (factorCap - oneReserve) tcap := by
  apply bellman_of_budget oneStart (factorCap - oneReserve) tcap oneOrder oneOrder_pos
    (fun _ hj => oneOrder_mono hj) _ (fun a ha _ hb => hprice a ha hb)
  intro x _ hx
  have hj : 3 + x.j ≤ 48 := hx.2.1
  by_cases hsmall : x.j ≤ 3
  · exact Or.inl (ite_eq_left hsmall)
  · have h := horder x.j (by omega) (by omega)
    exact Or.inr <| (availableMass_anti_prefix (x := x) (y := ⟨0, x.j, 0⟩)
      (Or.inr (by decide)) (by change 0 < 3 + x.j; omega)
      (Nat.zero_le x.b) le_rfl).trans_lt h

private theorem two_bellman (tcap : ℕ) (horder : c6) (hprice : c7) :
    Bellman twoStart (factorCap - twoReserve) tcap := by
  apply bellman_of_budget twoStart (factorCap - twoReserve) tcap twoOrder
    (by intro x; unfold twoOrder; split_ifs <;> decide)
    (by intro x y _ hj; unfold twoOrder; split_ifs <;> omega) _ (fun a ha _ hb => hprice a ha hb)
  intro x hx hbox
  have hj : 3 ≤ x.j := (Nat.mul_le_mul_left 3 hx.1).trans hx.2.1
  have hu : 6 + x.j ≤ 48 := hbox.2.1
  exact Or.inr <| (availableMass_anti_prefix (x := x) (y := ⟨0,x.j,0⟩)
    (Or.inr (by decide)) (by change 0 < 6 + x.j; omega) (Nat.zero_le _) le_rfl).trans_lt
      (horder _ hj (by omega))


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
    {z : Finset ι} (hretained : c1) (ha : ∀ i, Valid (a i)) (hbox : RetainedBox27 (shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ P0_9.fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤
      (if (shapeSum a z).t = 1 then oneReserve else 55500000000000000) *
        (shapeSum a z).t := by
  let r := shapeSum a z
  let rate : ℕ := if r.t = 1 then oneReserve else 55500000000000000
  change (∑ i ∈ z, cost i) ≤ rate * ∑ i ∈ z, (a i).t
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hle : InBox (a i) r := inBox_shapeSum a hi
  have hsmall := retainedBox_down hle hbox
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
  let tcap := ∑ i, (a i).t
  have cap_min : factorCap ≤ P0_9.factorPrice tcap := by
    unfold P0_9.factorPrice
    split_ifs <;> decide
  have account : ∃ (q : Shape) (cap : ℕ), InBox q r ∧ (q = zeroShape ∨ 0 < q.j) ∧
      Bellman q cap tcap ∧ (∑ i ∈ z, cost i) + cap ≤ P0_9.factorPrice tcap := by
    rcases shapeSum_valid_or_empty ha z with hempty | hr
    · have hr0 : r = zeroShape := by simp [r, hempty, shapeSum_empty]
      refine ⟨zeroShape, P0_9.factorPrice tcap, ?_, Or.inl rfl, empty_bellman tcap h2 h3, ?_⟩
      · rw [hr0]
        exact ⟨le_rfl, le_rfl, le_rfl⟩
      · simp [hempty]
    · have hmass := mass_le hlayers (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
        (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
      have hret : RetainedBox27 r := retained_bound symbol_count hr
        (by simpa [layerTerm, shapeSum_empty, zeroShape] using hmass)
      have hcost := retained_cost h1 ha hret hfat
      have htr : 1 ≤ r.t := hr.1
      have hjr : 3 * r.t ≤ r.j := hr.2.1
      have hbr : r.j ≤ 3 * r.b := hr.2.2
      have hrj : r.j ≤ 6 := hret.2.1
      have ht : r.t = 1 ∨ r.t = 2 := by omega
      rcases ht with ht | ht
      · refine ⟨oneStart, factorCap - oneReserve, ?_, Or.inr (by decide), one_bellman tcap h4 h5, ?_⟩
        · change 1 ≤ r.b ∧ 3 ≤ r.j ∧ 1 ≤ r.t
          omega
        · change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then _ else _) * r.t at hcost
          rw [ite_eq_left ht, ht, Nat.mul_one] at hcost
          exact ((Nat.add_le_add_right hcost _).trans (by decide : _ ≤ factorCap)).trans cap_min
      · refine ⟨twoStart, factorCap - twoReserve, ?_, Or.inr (by decide), two_bellman tcap h6 h7, ?_⟩
        · change 2 ≤ r.b ∧ 6 ≤ r.j ∧ 2 ≤ r.t
          omega
        · change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then _ else _) * r.t at hcost
          rw [ite_eq_right (by omega : r.t ≠ 1), ht] at hcost
          have hreserve : (∑ i ∈ z, cost i) ≤ twoReserve := hcost.trans (by decide)
          exact ((Nat.add_le_add_right hreserve _).trans (by decide : _ ≤ factorCap)).trans cap_min
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
        have htcap : (a i).t ≤ tcap := Finset.single_le_sum (fun j _ => Nat.zero_le (a j).t) (Finset.mem_univ i)
        exact hB _ _ hvalid (ha i) htcap hc
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
  change (∑ i, cost i) ≤ P0_9.factorPrice tcap
  omega

end P0_9_8
end PackSource_P0_9_8Split


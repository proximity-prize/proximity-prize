import ProximityPrize.SubmissionLower.PortLowBase
import ProximityPrize.SubmissionLower.RungFront
set_option autoImplicit true
section
namespace P0_9_8
open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape fullCap availableMass)
open K1_13_8_2 (Threshold orderFor)
abbrev oneStart : Shape := ⟨1, 3, 1⟩
abbrev twoStart : Shape := ⟨2, 6, 2⟩
def oneOrder (x : Shape) : ℕ := if x.j ≤ 3 then 1 else (3 * x.j - 4) / 2
def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (48 - r.j)
end P0_9_8
end
section
namespace P0_9_8
open K1_13 (Shape InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape fullCap availableMass layerTerm)
open K1_13_8_2 (Threshold orderFor)
open scoped BigOperators
theorem symbol_count : ∀ b j, remaining b j = K1_13_8.fastRemaining b j :=
  K1_13_8_1.proof
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
end P0_9_8
end
section
namespace P0_9_8_3
open K1_13
open K1_13_8_2 (Chamber mixed_mono)
end P0_9_8_3
end
section
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
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
end P0_9_8_5
end

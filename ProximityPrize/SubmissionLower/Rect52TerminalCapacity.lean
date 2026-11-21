import ProximityPrize.SubmissionLower.High52Family
import ProximityPrize.SubmissionLower.Rect51Rank
import ProximityPrize.SubmissionLower.RectAsymmetricSlots

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Rect52Terminal
open Finset Polynomial K1_14
open K1_14_4 (gradeWidth)
open High52 (agreement contactPower)
open scoped BigOperators
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
open private sum_slot_drops sum_interval power_threshold from ProximityPrize.SubmissionLower.Fast072

/-- Available seed coefficients after division along the two seed coordinates. -/
def slots (u v x y r : ℕ) : ℕ := (u+1-r*x)*(v+1-r*y)

theorem slots_antitone (u v x y : ℕ) : Antitone (slots u v x y) := by
  intro a b hab
  exact Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_right x hab) _)
    (Nat.sub_le_sub_left (Nat.mul_le_mul_right y hab) _)

theorem box_slots_eq (u v x y : ℕ) : Rect51Rank.slots u v x y = slots u v x y 1 := by
  by_cases hx : x ≤ u <;> by_cases hy : y ≤ v <;>
    unfold Rect51Rank.slots slots <;> simp only [one_mul]
  all_goals
    first
    | rw [ite_eq_left (by omega : x≤u ∧ y≤v), Nat.sub_add_comm (by omega : x ≤ u), Nat.sub_add_comm (by omega : y ≤ v)]
    | rw [ite_eq_right (by omega : ¬ (x≤u ∧ y≤v))]
      first | rw [Nat.sub_eq_zero_of_le (by omega : u+1≤x), Nat.zero_mul] | rw [Nat.sub_eq_zero_of_le (by omega : v+1≤y), Nat.mul_zero]

def kept (c : ℕ → ℕ) (g r : ℕ) : ℕ := if r ≤ g then c r else 0

def cutoffCapacity (h : ℕ) (s : Shape) (E : ℕ) (c : ℕ → ℕ) (W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then kept c ((q-j)/E) (contactPower h s W - j) else 0

def gradeCapacity (h : ℕ) (s : Shape) (E : ℕ) (c : ℕ → ℕ) (W j : ℕ) : ℕ :=
  let r := contactPower h s W - j
  (gradeWidth (131071-h) s.B W j - r*E) * c r

/-- Coefficient loss from the cutoff rank bound, for any decreasing slot count. -/
def jointGain (h : ℕ) (s : Shape) (E : ℕ) (c : ℕ → ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    (∑ a ∈ range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

private theorem gradeCapacity_eq (k B W j r E : ℕ) (c : ℕ → ℕ) (hk : 0 < k) (he : 0 < E) :
    (gradeWidth k B W j - r*E) * c r =
      ∑ q ∈ Ico j (B+1), if q*k ≤ W+j then kept c ((q-j)/E) r else 0 := by
  have hq (q : ℕ) : q*k ≤ W+j ↔ q < (W+j)/k + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk]
  have hr (q : ℕ) : r ≤ (q-j)/E ↔ r*E ≤ q-j := Nat.le_div_iff_mul_le he
  have hI : (Ico j (B+1)).filter (fun q => q*k ≤ W+j ∧ r ≤ (q-j)/E) =
      Ico (j + r*E) (min (B+1) ((W+j)/k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, hq, hr, lt_min_iff]
    omega
  simp_rw [kept, ← ite_and]
  rw [← sum_filter, hI, sum_const, Nat.nsmul_eq_mul, Nat.card_Ico, gradeWidth, Nat.sub_sub]

theorem cutoffCapacity_eq (h : ℕ) (s : Shape) (E : ℕ) (c : ℕ → ℕ) (W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), gradeCapacity h s E c W j) = cutoffCapacity h s E c W := by
  rw [cutoffCapacity, ← shapeSum_swap]
  apply sum_congr rfl
  intro j _
  exact gradeCapacity_eq _ _ _ _ _ _ _ hk he

private theorem position_sum (top step t j g : ℕ) (c : ℕ → ℕ) (hc : Antitone c) (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then
      kept c g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (c a - c (a+1)) * (top+j-t-step*(j+a))) +
      c g * (top+j-t-step*(j+g))) =
    c 0 * (top+j-t) := by
  let A := kept c g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone A := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [A, kept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        hc hab
    · simp [A, kept, hb]
  have hmin (l : ℕ) : A (min (g+1) l) = A l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [A, kept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (A a - A (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (c a - c (a+1)) * (top+j-t-step*(j+a))) +
        c g * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [A, kept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [A, kept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then A (L W) else 0) + _ = _
  have hzero : A 0 = c 0 := by simp [A, kept]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (A 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops A hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]
theorem cutoff_total (h : ℕ) (s : Shape) (E : ℕ) (c : ℕ → ℕ) (hc : Antitone c) (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*agreement), cutoffCapacity h s E c W) + jointGain h s E c =
      c 0 * shapeSum s (fun q j => s.m*agreement+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*agreement), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*agreement), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [cutoffCapacity, jointGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum (s.m*agreement) (2*h) (q*(131071-h)) j ((q-j)/E) c hc
    (hjq.trans hq) hh

open K1_14 (FX Equation Jet)
open Rect51Rank (coordDegree coordDegree_pow rank_multiples_le)
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069

theorem cutoff_finrank_le (h : ℕ) (s : Shape) (u v E W : ℕ) (c : ℕ → ℕ) (C : Submodule FX Jet)
    {f : Equation} (hf : f≠0) (hE : E≤f.natDegree)
    (hslots : ∀ r, Rect51Rank.slots u v (r*coordDegree f (some 0))
      (r*coordDegree f (some 1)) ≤ c r) (hk : 0<131071-h)
    (hshape : ∀ P∈C, P≠0 → P.leadingCoeff.natDegree+P.natDegree≤s.B∧P.natDegree≤s.J)
    (hbox : ∀ P∈C,
      coordDegree P.leadingCoeff (some 0)≤u ∧ coordDegree P.leadingCoeff (some 1)≤v)
    (hlead : ∀ P∈C, P≠0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P∈C, P≠0 → f^(contactPower h s W-P.natDegree)∣P.leadingCoeff) :
    Module.finrank FX C≤∑ j∈range (s.J+1),gradeCapacity h s E c W j := by
  refine finrank_le_grades (F := FX) (A := Equation) C (gradeCapacity h s E c W)
    (s.J+1) ?_ ?_
  · intro j
    let r := contactPower h s W - j
    let a := gradeWidth (131071-h) s.B W j
    let x := coordDegree f (some 0)
    let y := coordDegree f (some 1)
    have hy := Nat.mul_le_mul_left r hE
    have hfPow : f^r≠0 := pow_ne_zero _ hf
    have hwn := show r*E ≤ (f^r).natDegree by rwa [natDegree_pow]
    have h0 := show r*x ≤ coordDegree (f^r) (some 0) by rw [coordDegree_pow hf]
    have h1 := show r*y ≤ coordDegree (f^r) (some 1) by rw [coordDegree_pow hf]
    refine (rank_multiples_le _ hfPow (a := a) (u0 := u) (u1 := v) hwn h0 h1 ?_).trans ?_
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := fun hz => hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      have hB := (hshape P hpV hn).1
      have hW := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hW hdiv
      change (P.coeff j).natDegree < a ∧ coordDegree (P.coeff j) (some 0)≤u ∧
        coordDegree (P.coeff j) (some 1)≤v ∧ f^r ∣ P.coeff j
      rw [← hj,coeff_natDegree]
      refine ⟨?_,(hbox P hpV).1,(hbox P hpV).2,hdiv⟩
      have hq := (Nat.le_div_iff_mul_le hk).2 hW
      unfold a gradeWidth
      omega
    · exact_mod_cast Nat.mul_le_mul_left (a-r*E) (hslots r)
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hshape P hp hn).2)

end Rect52Terminal

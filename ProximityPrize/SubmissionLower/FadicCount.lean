import ProximityPrize.SubmissionLower.PrimaryTaperColumns

set_option Elab.async false

/-!
# Exact counts of tapered boxes of jet exponents

`taperBox B J T Θ` is the set of jet exponents with grade at most `B`, index at most `J`, top
exponent at most `T` and `26·grade + 25·(e₁+e₂+e₃) ≤ Θ`.  With `Θ = 131312` and `B ≤ 4012`,
`J ≤ 1650` it lies inside the accepted `TaperColumns.jetExponents`.

* `taperBox_card`: its cardinality is `boxCount B J T Θ`, a sum of accepted `cappedCount`s over
  the grades.
* `fastCount_eq`: the same number with the constant middle range collapsed, for the kernel.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount cumulative denominator)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns cumulativeExponents
  mem_cumulativeColumns)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open TaperColumns (sumGrade sumOld)

/-- Jet exponents in a box with the linear taper. -/
def taperBox (B J T Θ : ℕ) : Set JetExp :=
  {e | Finsupp.weight gradeWeight e ≤ B ∧ Finsupp.weight oldWeight e ≤ J ∧ e 3 ≤ T ∧
    26 * Finsupp.weight gradeWeight e + 25 * (e 1 + e 2 + e 3) ≤ Θ}

theorem taperBox_finite (B J T Θ : ℕ) : (taperBox B J T Θ).Finite :=
  (Finsupp.finite_of_nat_weight_le gradeWeight (fun j => by simp [gradeWeight]) B).subset
    (fun _ h => h.1)


/-- The largest non-`Y₀` degree allowed at grade `q`. -/
def padGrade (Θ q : ℕ) : ℕ := min q ((Θ - 26 * q) / 25)

/-- The count at one grade. -/
def term (J T Θ q : ℕ) : ℤ :=
  if 26 * q ≤ Θ then cappedCount (padGrade Θ q) J T else 0

/-- The exact number of exponents in `taperBox B J T Θ`. -/
def boxCount (B J T Θ : ℕ) : ℤ := ∑ q ∈ range (B + 1), term J T Θ q

private noncomputable def grid (B J T Θ : ℕ) : Finset (Σ _ : ℕ, JetExp) :=
  ((range (B + 1)).filter fun q => 26 * q ≤ Θ).sigma fun q => cappedColumns (padGrade Θ q) J T

private noncomputable def pad (Θ : ℕ) (x : Σ _ : ℕ, JetExp) : JetExp :=
  x.2 + Finsupp.single 0 (x.1 - padGrade Θ x.1)

private theorem grid_mem {B J T Θ : ℕ} {q : ℕ} {m : JetExp} (hx : (⟨q, m⟩ : Σ _ : ℕ, JetExp) ∈ grid B J T Θ) :
    q ≤ B ∧ 26 * q ≤ Θ ∧ Finsupp.weight gradeWeight m = padGrade Θ q ∧
      Finsupp.weight oldWeight m ≤ J ∧ m 3 ≤ T := by
  obtain ⟨hq, hm⟩ := mem_sigma.mp hx
  obtain ⟨hr, hΘ⟩ := mem_filter.mp hq
  obtain ⟨hj, ht⟩ := mem_cappedColumns.mp hm
  obtain ⟨hg, hi⟩ := mem_cumulativeColumns.mp hj
  refine ⟨Nat.lt_succ_iff.mp (mem_range.mp hr), hΘ, ?_, ?_, ?_⟩
  · exact_mod_cast hg
  · exact_mod_cast hi
  · exact_mod_cast ht

private theorem pad_apply_zero (Θ q : ℕ) (m : JetExp) :
    pad Θ ⟨q, m⟩ 0 = m 0 + (q - padGrade Θ q) := by simp [pad]

private theorem pad_apply_ne (Θ q : ℕ) (m : JetExp) (i : Fin 4) (hi : i ≠ 0) :
    pad Θ ⟨q, m⟩ i = m i := by simp [pad, Finsupp.single_eq_of_ne hi]

private theorem pad_grade {B J T Θ : ℕ} {q : ℕ} {m : JetExp}
    (hx : (⟨q, m⟩ : Σ _ : ℕ, JetExp) ∈ grid B J T Θ) :
    Finsupp.weight gradeWeight (pad Θ ⟨q, m⟩) = q := by
  obtain ⟨_, _, hg, _, _⟩ := grid_mem hx
  have hle : padGrade Θ q ≤ q := min_le_left _ _
  rw [sumGrade, pad_apply_zero, pad_apply_ne _ _ _ 1 (by decide), pad_apply_ne _ _ _ 2 (by decide),
    pad_apply_ne _ _ _ 3 (by decide)]
  rw [sumGrade] at hg
  omega

private theorem pad_mem {B J T Θ : ℕ} {x : Σ _ : ℕ, JetExp} (hx : x ∈ grid B J T Θ) :
    pad Θ x ∈ (taperBox_finite B J T Θ).toFinset := by
  obtain ⟨q, m⟩ := x
  obtain ⟨hq, hΘ, hg, hi, ht⟩ := grid_mem hx
  have hgrade := pad_grade hx
  have hdiv : (Θ - 26 * q) / 25 * 25 ≤ Θ - 26 * q := Nat.div_mul_le_self _ _
  have hpg : padGrade Θ q ≤ (Θ - 26 * q) / 25 := min_le_right _ _
  apply (taperBox_finite B J T Θ).mem_toFinset.mpr
  refine ⟨hgrade.le.trans hq, ?_, ?_, ?_⟩
  · rw [sumOld, pad_apply_ne _ _ _ 1 (by decide), pad_apply_ne _ _ _ 2 (by decide),
      pad_apply_ne _ _ _ 3 (by decide), ← sumOld]
    exact hi
  · rw [pad_apply_ne _ _ _ 3 (by decide)]
    exact ht
  · rw [hgrade, pad_apply_ne _ _ _ 1 (by decide), pad_apply_ne _ _ _ 2 (by decide),
      pad_apply_ne _ _ _ 3 (by decide)]
    rw [sumGrade] at hg
    omega

private theorem pad_injOn (B J T Θ : ℕ) :
    Set.InjOn (pad Θ) (grid B J T Θ : Set (Σ _ : ℕ, JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨q, m⟩ := x
  obtain ⟨q', m'⟩ := y
  have eQ : q = q' :=
    (pad_grade hx).symm.trans ((congrArg (fun e : JetExp => Finsupp.weight gradeWeight e) hxy).trans
      (pad_grade hy))
  subst q'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q - padGrade Θ q))
    exact hxy
  subst m'
  rfl

private theorem pad_surj {B J T Θ : ℕ} {e : JetExp} (he : e ∈ taperBox B J T Θ) :
    ∃ x ∈ grid B J T Θ, pad Θ x = e := by
  obtain ⟨hB, hJ, hT, hΘ⟩ := he
  set q := Finsupp.weight gradeWeight e with hq
  have hsum := sumGrade e
  have hold := sumOld e
  have h26 : 26 * q ≤ Θ := le_trans (Nat.le_add_right _ _) hΘ
  have hd : e 1 + e 2 + e 3 ≤ padGrade Θ q := by
    apply le_min
    · omega
    · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
      omega
  have hpq : padGrade Θ q ≤ q := min_le_left _ _
  let m : JetExp := e - Finsupp.single 0 (q - padGrade Θ q)
  have m0 : m 0 = e 0 - (q - padGrade Θ q) := by simp [m]
  have mi (i : Fin 4) (hi : i ≠ 0) : m i = e i := by simp [m, Finsupp.single_eq_of_ne hi]
  have hmg : Finsupp.weight gradeWeight m = padGrade Θ q := by
    rw [sumGrade, m0, mi 1 (by decide), mi 2 (by decide), mi 3 (by decide)]
    omega
  have hmo : Finsupp.weight oldWeight m = Finsupp.weight oldWeight e := by
    rw [sumOld, sumOld, mi 1 (by decide), mi 2 (by decide), mi 3 (by decide)]
  refine ⟨⟨q, m⟩, ?_, ?_⟩
  · apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hB), h26⟩, ?_⟩
    apply mem_cappedColumns.mpr
    refine ⟨mem_cumulativeColumns.mpr ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hmg
    · rw [hmo]
      exact_mod_cast hJ
    · rw [mi 3 (by decide)]
      exact_mod_cast hT
  · ext i
    by_cases hi : i = 0
    · subst hi
      rw [pad_apply_zero, m0]
      omega
    · rw [pad_apply_ne _ _ _ i hi, mi i hi]

/-- **Exact count.** -/
theorem taperBox_card (B J T Θ : ℕ) :
    (((taperBox_finite B J T Θ).toFinset.card : ℕ) : ℤ) = boxCount B J T Θ := by
  classical
  have himage : (taperBox_finite B J T Θ).toFinset = (grid B J T Θ).image (pad Θ) := by
    ext e
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := pad_surj ((taperBox_finite B J T Θ).mem_toFinset.mp he)
      exact mem_image_of_mem _ hx
    · intro he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      exact pad_mem hx
  rw [himage, card_image_of_injOn (pad_injOn B J T Θ)]
  unfold grid boxCount
  rw [card_sigma, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  unfold term
  split
  · exact capped_card K1_13_2_2_2.proof _ _ _
  · rfl

/-! ### The kernel-friendly form -/

private theorem denominator_neg {u : ℤ} (h : u < 0) : denominator u = 0 := by
  unfold denominator
  simp [h]

private theorem cumulative_neg (d : ℤ) {u : ℤ} (h : u < 0) : cumulative d u = 0 := by
  unfold cumulative
  simp [h]

private theorem cumulative_flat {d u : ℤ} (hu : 0 ≤ u) (hd : u ≤ d) :
    cumulative d u = denominator u := by
  unfold cumulative
  have h1 : ¬ d < 0 := by omega
  have h2 : ¬ u < 0 := by omega
  have hv : min u (3 * d) = u := min_eq_left (by omega)
  simp only [h1, h2, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hv]
  rw [denominator_neg (by omega : u - d - 1 < 0), denominator_neg (by omega : u - d - 2 < 0),
    denominator_neg (by omega : u - d - 3 < 0), denominator_neg (by omega : u - 2 * d - 3 < 0),
    denominator_neg (by omega : u - 2 * d - 4 < 0), denominator_neg (by omega : u - 2 * d - 5 < 0),
    denominator_neg (by omega : u - 3 * d - 6 < 0)]
  ring

/-- Above the index bound the count no longer depends on the degree. -/
theorem cappedCount_flat {d u t : ℤ} (hu : 0 ≤ u) (hd : u ≤ d) :
    cappedCount d u t = cappedCount u u t := by
  unfold cappedCount
  by_cases ht : t < 0
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    rw [cumulative_flat hu hd, cumulative_flat hu le_rfl]
    by_cases hneg : u - 3 * (t + 1) < 0
    · rw [cumulative_neg _ hneg, cumulative_neg _ hneg]
    · rw [cumulative_flat (by omega) (by omega), cumulative_flat (by omega) (by omega)]

/-- A prefix sum the kernel evaluates by structural recursion. -/
def intPrefix (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => intPrefix f n + f n

theorem intPrefix_eq (f : ℕ → ℤ) (n : ℕ) : intPrefix f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [intPrefix]
  | succ n ih => rw [intPrefix, sum_range_succ, ih]

/-- First grade of the constant range. -/
def flatLo (B J : ℕ) : ℕ := min J (B + 1)

/-- One past the last grade of the constant range `J ≤ q`, `26 q + 25 J ≤ Θ`. -/
def flatHi (B J Θ : ℕ) : ℕ :=
  if 25 * J ≤ Θ then max (flatLo B J) (min (B + 1) ((Θ - 25 * J) / 26 + 1)) else flatLo B J

/-- `boxCount` with the constant range collapsed to one product. -/
def fastCount (B J T Θ : ℕ) : ℤ :=
  intPrefix (term J T Θ) (flatLo B J) +
    ((flatHi B J Θ - flatLo B J : ℕ) : ℤ) * cappedCount J J T +
    intPrefix (fun i => term J T Θ (flatHi B J Θ + i)) (B + 1 - flatHi B J Θ)

theorem fastCount_eq (B J T Θ : ℕ) : fastCount B J T Θ = boxCount B J T Θ := by
  have hlo_le : flatLo B J ≤ B + 1 := min_le_right _ _
  have hlohi : flatLo B J ≤ flatHi B J Θ := by
    unfold flatHi
    split
    · exact le_max_left _ _
    · exact le_rfl
  have hhi_le : flatHi B J Θ ≤ B + 1 := by
    unfold flatHi
    split
    · exact max_le hlo_le (min_le_left _ _)
    · exact hlo_le
  have hmid : (∑ k ∈ range (flatHi B J Θ - flatLo B J), term J T Θ (flatLo B J + k)) =
      ((flatHi B J Θ - flatLo B J : ℕ) : ℤ) * cappedCount J J T := by
    suffices hconst : ∀ k ∈ range (flatHi B J Θ - flatLo B J),
        term J T Θ (flatLo B J + k) = cappedCount J J T by
      rw [sum_congr rfl hconst, sum_const, card_range, nsmul_eq_mul]
    intro k hk
    have hk' : k < flatHi B J Θ - flatLo B J := mem_range.mp hk
    have hcond : 25 * J ≤ Θ := by
      by_contra hc
      have : flatHi B J Θ = flatLo B J := by unfold flatHi; rw [if_neg hc]
      omega
    have hhi : flatHi B J Θ = max (flatLo B J) (min (B + 1) ((Θ - 25 * J) / 26 + 1)) := by
      unfold flatHi; rw [if_pos hcond]
    have hlt : flatLo B J + k < min (B + 1) ((Θ - 25 * J) / 26 + 1) := by
      have h1 : flatLo B J + k < max (flatLo B J) (min (B + 1) ((Θ - 25 * J) / 26 + 1)) := by
        omega
      rcases lt_max_iff.mp h1 with h | h
      · omega
      · exact h
    have hB : flatLo B J < B + 1 := lt_of_le_of_lt (Nat.le_add_right _ k)
      (lt_of_lt_of_le hlt (min_le_left _ _))
    have hloJ : flatLo B J = J := by
      unfold flatLo at hB ⊢
      apply min_eq_left
      by_contra hc
      rw [min_eq_right (by omega)] at hB
      exact lt_irrefl _ hB
    have hq2 : flatLo B J + k ≤ (Θ - 25 * J) / 26 := by
      have := lt_of_lt_of_le hlt (min_le_right _ _)
      omega
    have h26 : 26 * (flatLo B J + k) ≤ Θ - 25 * J :=
      (Nat.mul_le_mul_left 26 hq2).trans (Nat.mul_div_le _ _)
    have hΘ : 26 * (flatLo B J + k) ≤ Θ := h26.trans (Nat.sub_le _ _)
    have hJle : J ≤ padGrade Θ (flatLo B J + k) := by
      apply le_min
      · omega
      · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
        omega
    unfold term
    rw [if_pos hΘ]
    exact cappedCount_flat (by positivity) (by exact_mod_cast hJle)
  have hsplit : B + 1 = flatLo B J + (flatHi B J Θ - flatLo B J) + (B + 1 - flatHi B J Θ) := by
    omega
  have hlast : (∑ x ∈ range (B + 1 - flatHi B J Θ),
      term J T Θ (flatLo B J + (flatHi B J Θ - flatLo B J) + x)) =
      ∑ x ∈ range (B + 1 - flatHi B J Θ), term J T Θ (flatHi B J Θ + x) := by
    refine sum_congr rfl fun x _ => ?_
    congr 1
    omega
  unfold fastCount boxCount
  rw [intPrefix_eq, intPrefix_eq]
  conv_rhs => rw [hsplit, sum_range_add, sum_range_add]
  rw [hmid, hlast]

end FadicGate

#print axioms FadicGate.taperBox_card
#print axioms FadicGate.fastCount_eq

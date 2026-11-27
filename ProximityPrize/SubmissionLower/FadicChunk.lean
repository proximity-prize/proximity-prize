import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily

set_option Elab.async false

-- merged module FadicDegree
section Merged_FadicDegree
set_option Elab.async false

-- merged module FadicCount
section Merged_FadicCount
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
def taperBox (B J T Θ : ℕ) : Set JetExp :=
  {e | Finsupp.weight gradeWeight e ≤ B ∧ Finsupp.weight oldWeight e ≤ J ∧ e 3 ≤ T ∧
    26 * Finsupp.weight gradeWeight e + 25 * (e 1 + e 2 + e 3) ≤ Θ}
theorem taperBox_finite (B J T Θ : ℕ) : (taperBox B J T Θ).Finite :=
  (Finsupp.finite_of_nat_weight_le gradeWeight (fun j => by simp [gradeWeight]) B).subset
    (fun _ h => h.1)
def padGrade (Θ q : ℕ) : ℕ := min q ((Θ - 26 * q) / 25)
def term (J T Θ q : ℕ) : ℤ :=
  if 26 * q ≤ Θ then cappedCount (padGrade Θ q) J T else 0
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
def intPrefix (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => intPrefix f n + f n
theorem intPrefix_eq (f : ℕ → ℤ) (n : ℕ) : intPrefix f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [intPrefix]
  | succ n ih => rw [intPrefix, sum_range_succ, ih]
def flatLo (B J : ℕ) : ℕ := min J (B + 1)
def flatHi (B J Θ : ℕ) : ℕ :=
  if 25 * J ≤ Θ then max (flatLo B J) (min (B + 1) ((Θ - 25 * J) / 26 + 1)) else flatLo B J
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

end Merged_FadicCount

-- merged module FadicSpace
section Merged_FadicSpace
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents)
open MvPolynomial
open scoped BigOperators
open Finset
def topWeight : Fin 4 → ℕ := fun i => if i = 3 then 1 else 0
def taperWeight : Fin 4 → ℕ := fun i => if i = 0 then 26 else 51
theorem weight_four (w : Fin 4 → ℕ) (m : JetExp) :
    Finsupp.weight w m = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp [Fin.sum_univ_four]
theorem w_grade (m : JetExp) : Finsupp.weight gradeWeight m = m 0 + m 1 + m 2 + m 3 := by
  rw [weight_four]; simp [gradeWeight]
theorem w_old (m : JetExp) : Finsupp.weight oldWeight m = m 1 + 2 * m 2 + 3 * m 3 := by
  rw [weight_four]; simp [oldWeight]; omega
theorem w_top (m : JetExp) : Finsupp.weight topWeight m = m 3 := by
  rw [weight_four]; simp [topWeight]
theorem w_taper (m : JetExp) :
    Finsupp.weight taperWeight m = 26 * m 0 + 51 * (m 1 + m 2 + m 3) := by
  rw [weight_four]; simp [taperWeight]; omega
section Field
variable {𝕜 : Type*} [Field 𝕜]
local notation "R" => MvPolynomial (Fin 4) 𝕜
theorem wdeg_le_of_support (w : Fin 4 → ℕ) (p : R) (b : ℕ)
    (h : ∀ m ∈ p.support, Finsupp.weight w m ≤ b) : p.weightedTotalDegree w ≤ b := by
  unfold MvPolynomial.weightedTotalDegree
  exact Finset.sup_le h
theorem wdeg_pow (w : Fin 4 → ℕ) {p : R} (hp : p ≠ 0) (a : ℕ) :
    (p ^ a).weightedTotalDegree w = a * p.weightedTotalDegree w := by
  induction a with
  | zero => rw [pow_zero, zero_mul, ← MvPolynomial.C_1, weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ, weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]
def DepthOK (xb xj r a : ℕ) : Prop :=
  3 * a ≤ r ∧ a < r ∧ a * xb ≤ 4012 ∧ a * xj ≤ 1650 ∧ a * (26 * xb + 25 * xj) ≤ 131312
instance (xb xj r a : ℕ) : Decidable (DepthOK xb xj r a) := by unfold DepthOK; infer_instance
private theorem shift_sum (f : R) (n : ℕ) (u : ℕ → R) :
    (∑ i ∈ range n, f ^ (i + 1) * u (i + 1)) = f * ∑ i ∈ range n, f ^ i * u (i + 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem fadic_zero (f : R) (hf : f ≠ 0) :
    ∀ (n : ℕ) (u : ℕ → R), (∀ i < n, f ∣ u i → u i = 0) →
      (∑ i ∈ range n, f ^ i * u i) = 0 → ∀ i < n, u i = 0 := by
  intro n
  induction n with
  | zero => intro u _ _ i hi; omega
  | succ n ih =>
    intro u hu h
    rw [Finset.sum_range_succ', shift_sum, pow_zero, one_mul] at h
    have h0 : u 0 = 0 :=
      hu 0 (Nat.succ_pos n) ⟨-(∑ i ∈ range n, f ^ i * u (i + 1)), by linear_combination h⟩
    rw [h0, add_zero] at h
    have hT : (∑ i ∈ range n, f ^ i * u (i + 1)) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hf
      · exact h1
    have hshift := ih (fun i => u (i + 1))
      (fun i hi hdiv => hu (i + 1) (Nat.succ_lt_succ hi) hdiv) hT
    intro i hi
    cases i with
    | zero => exact h0
    | succ i => exact hshift i (Nat.lt_of_succ_lt_succ hi)
theorem fadic_shape (f : R) :
    ∀ (a n : ℕ) (u : ℕ → R), a < n → (∀ i < a, u i = 0) →
      ∃ h : R, (∑ i ∈ range n, f ^ i * u i) = f ^ a * (u a + f * h) := by
  intro a
  induction a with
  | zero =>
    intro n u hn _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨∑ i ∈ range m, f ^ i * u (i + 1), ?_⟩
    rw [Finset.sum_range_succ', shift_sum]
    ring
  | succ a ih =>
    intro n u hn hlow
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h, hh⟩ := ih m (fun i => u (i + 1)) (by omega)
      (fun i hi => hlow (i + 1) (by omega))
    refine ⟨h, ?_⟩
    rw [Finset.sum_range_succ', shift_sum, hlow 0 (Nat.succ_pos a), hh]
    ring
end Field
end FadicGate

end Merged_FadicSpace

-- merged module FadicGateDim
section Merged_FadicGateDim
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset
def IsFull (σb σj σt r : ℕ) : Prop := 4012 ≤ r * σb ∧ 1650 ≤ r * σj ∧ 550 ≤ r * σt
instance (σb σj σt r : ℕ) : Decidable (IsFull σb σj σt r) := by unfold IsFull; infer_instance
def slopeBox (B J T : ℕ) : Set JetExp :=
  {e | Finsupp.weight gradeWeight e ≤ B ∧ Finsupp.weight oldWeight e ≤ J ∧ e 3 ≤ T}
theorem taperBox_subset_slopeBox (B J T Θ : ℕ) : taperBox B J T Θ ⊆ slopeBox B J T :=
  fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
theorem taperBox_subset_source {B J T : ℕ} (hB : B ≤ 4012) (hJ : J ≤ 1650) :
    taperBox B J T 131312 ⊆ jetExponents := by
  intro e he
  obtain ⟨h1, h2, _, h4⟩ := he
  have hg := w_grade e
  have ho := w_old e
  refine ⟨h1.trans hB, h2.trans hJ, ?_⟩
  unfold TaperBudget.cap
  split
  · omega
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
    omega
theorem source_subset_slopeBox {σb σj σt r : ℕ} (h : IsFull σb σj σt r) :
    jetExponents ⊆ slopeBox (r * σb) (r * σj) (r * σt) := by
  intro e he
  obtain ⟨h1, h2, _⟩ := he
  obtain ⟨hb, hj, ht⟩ := h
  have ho := w_old e
  exact ⟨h1.trans hb, h2.trans hj, by omega⟩
section Field
variable {𝕜 : Type*} [Field 𝕜]
end Field
end FadicGate

end Merged_FadicGateDim

-- merged module FadicVar
section Merged_FadicVar
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset
abbrev Entry := Option (ℕ × ℕ × ℕ)
def varΘ (H a : ℕ) : ℕ := 131312 - a * H
def BoxOK (bh jh H a B J : ℕ) : Prop := B + a * bh ≤ 4012 ∧ J + a * jh ≤ 1650 ∧ a * H ≤ 131312
instance (bh jh H a B J : ℕ) : Decidable (BoxOK bh jh H a B J) := by unfold BoxOK; infer_instance
def varMult (bl jl tl L B J T Θ : ℕ) : ℤ :=
  if bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ then boxCount (B - bl) (J - jl) (T - tl) (Θ - L) else 0
def varDepthDim (bl bh jl jh tl L H a : ℕ) : Entry → ℤ
  | none => 0
  | some (B, J, T) =>
    if BoxOK bh jh H a B J then
      max 0 (boxCount B J T (varΘ H a) - varMult bl jl tl L B J T (varΘ H a))
    else 0
def varFadicDim (bl bh jl jh tl L H n : ℕ) (box : ℕ → Entry) : ℤ :=
  ∑ a ∈ range n, varDepthDim bl bh jl jh tl L H a (box a)
section Field
variable {𝕜 : Type*} [Field 𝕜]
local notation "R" => MvPolynomial (Fin 4) 𝕜
theorem w_taper' (m : JetExp) :
    Finsupp.weight taperWeight m = 26 * Finsupp.weight gradeWeight m + 25 * (m 1 + m 2 + m 3) := by
  rw [w_taper, w_grade]
  ring
theorem pow_mul_mem_source_var (f : R) (hf : f ≠ 0) (bh jh H : ℕ)
    (hbh : f.weightedTotalDegree gradeWeight ≤ bh) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (hH : f.weightedTotalDegree taperWeight ≤ H)
    {B J T a : ℕ} (hB : B + a * bh ≤ 4012) (hJ : J + a * jh ≤ 1650) (hΘ : a * H ≤ 131312)
    {c : R} (hc : c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a))) :
    f ^ a * c ∈ restrictSupport 𝕜 jetExponents := by
  classical
  rw [mem_restrictSupport_iff] at hc ⊢
  intro m hm
  obtain ⟨μ, hμ, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  obtain ⟨heB, heJ, _, heΘ⟩ := hc he
  have hμg : Finsupp.weight gradeWeight μ ≤ a * bh := by
    refine (le_weightedTotalDegree gradeWeight hμ).trans ?_
    rw [wdeg_pow gradeWeight hf a]
    exact Nat.mul_le_mul_left a hbh
  have hμo : Finsupp.weight oldWeight μ ≤ a * jh := by
    refine (le_weightedTotalDegree oldWeight hμ).trans ?_
    rw [wdeg_pow oldWeight hf a]
    exact Nat.mul_le_mul_left a hjh
  have hμτ : Finsupp.weight taperWeight μ ≤ a * H := by
    refine (le_weightedTotalDegree taperWeight hμ).trans ?_
    rw [wdeg_pow taperWeight hf a]
    exact Nat.mul_le_mul_left a hH
  have hτ := w_taper' μ
  have ho := w_old μ
  have hoe := w_old e
  have hsumg : Finsupp.weight gradeWeight (μ + e) =
      Finsupp.weight gradeWeight μ + Finsupp.weight gradeWeight e := map_add _ _ _
  have hsumo : Finsupp.weight oldWeight (μ + e) =
      Finsupp.weight oldWeight μ + Finsupp.weight oldWeight e := map_add _ _ _
  unfold varΘ at heΘ
  change Finsupp.weight gradeWeight (μ + e) ≤ 4012 ∧ Finsupp.weight oldWeight (μ + e) ≤ 1650 ∧
    (μ + e) 1 + (μ + e) 2 + (μ + e) 3 ≤ TaperBudget.cap (Finsupp.weight gradeWeight (μ + e))
  rw [hsumg, hsumo]
  simp only [Finsupp.add_apply]
  refine ⟨by omega, by omega, ?_⟩
  unfold TaperBudget.cap
  split
  · omega
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
    omega
theorem cofactor_mem_var (f : R) (hf : f ≠ 0) (bl jl tl L : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hjl : jl ≤ f.weightedTotalDegree oldWeight)
    (htl : tl ≤ f.weightedTotalDegree topWeight) (hL : L ≤ f.weightedTotalDegree taperWeight)
    {B J T Θ : ℕ} {g : R} (hg : g ≠ 0)
    (hfg : f * g ∈ restrictSupport 𝕜 (taperBox B J T Θ)) :
    (bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ) ∧
      g ∈ restrictSupport 𝕜 (taperBox (B - bl) (J - jl) (T - tl) (Θ - L)) := by
  classical
  rw [mem_restrictSupport_iff] at hfg
  have hmul (w : Fin 4 → ℕ) : (f * g).weightedTotalDegree w =
      f.weightedTotalDegree w + g.weightedTotalDegree w := weightedTotalDegree_mul _ _ _ hf hg
  have hgB : (f * g).weightedTotalDegree gradeWeight ≤ B :=
    wdeg_le_of_support _ _ _ fun m hm => (hfg hm).1
  have hgJ : (f * g).weightedTotalDegree oldWeight ≤ J :=
    wdeg_le_of_support _ _ _ fun m hm => (hfg hm).2.1
  have hgT : (f * g).weightedTotalDegree topWeight ≤ T :=
    wdeg_le_of_support _ _ _ fun m hm => by rw [w_top]; exact (hfg hm).2.2.1
  have hgΘ : (f * g).weightedTotalDegree taperWeight ≤ Θ :=
    wdeg_le_of_support _ _ _ fun m hm => by
      have h := (hfg hm).2.2.2
      rw [w_taper']
      exact h
  rw [hmul] at hgB hgJ hgT hgΘ
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
  rw [mem_restrictSupport_iff]
  intro e he
  have h1 := le_weightedTotalDegree gradeWeight he
  have h2 := le_weightedTotalDegree oldWeight he
  have h3 := le_weightedTotalDegree topWeight he
  have h4 := le_weightedTotalDegree taperWeight he
  rw [w_top] at h3
  rw [w_taper'] at h4
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem exists_varDepthSpace (f : R) (hf : f ≠ 0) (bl bh jl jh tl L H : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (htl : tl ≤ f.weightedTotalDegree topWeight)
    (hL : L ≤ f.weightedTotalDegree taperWeight) (hH : f.weightedTotalDegree taperWeight ≤ H)
    (a : ℕ) (e : Entry) :
    ∃ C : Submodule 𝕜 R, FiniteDimensional 𝕜 C ∧
      varDepthDim bl bh jl jh tl L H a e ≤ (Module.finrank 𝕜 C : ℤ) ∧
      (∀ c ∈ C, f ∣ c → c = 0) ∧
      (∀ c ∈ C, f ^ a * c ∈ restrictSupport 𝕜 jetExponents) ∧
      (∀ c ∈ C, c ≠ 0 → ∃ B J T : ℕ, e = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
        c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a))) := by
  classical
  have bot_case : ∃ C : Submodule 𝕜 R, FiniteDimensional 𝕜 C ∧ (0 : ℤ) ≤ (Module.finrank 𝕜 C : ℤ) ∧
      (∀ c ∈ C, f ∣ c → c = 0) ∧ (∀ c ∈ C, f ^ a * c ∈ restrictSupport 𝕜 jetExponents) ∧
      (∀ c ∈ C, c ≠ 0 → ∃ B J T : ℕ, e = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
        c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a))) := by
    refine ⟨⊥, inferInstance, by positivity, ?_, ?_, ?_⟩
    · intro c hc _; exact (Submodule.mem_bot 𝕜).mp hc
    · intro c hc
      rw [(Submodule.mem_bot 𝕜).mp hc, mul_zero]
      exact Submodule.zero_mem _
    · intro c hc hne; exact absurd ((Submodule.mem_bot 𝕜).mp hc) hne
  rcases e with _ | ⟨B, J, T⟩
  · simpa [varDepthDim] using bot_case
  by_cases hok : BoxOK bh jh H a B J
  swap
  · simpa [varDepthDim, hok] using bot_case
  obtain ⟨hB, hJ, hΘa⟩ := hok
  set Θ := varΘ H a with hΘdef
  have hI := taperBox_finite B J T Θ
  let M : Submodule 𝕜 R := restrictSupport 𝕜 (taperBox B J T Θ)
  have : Module.Finite 𝕜 M := restrictSupport_finite hI
  have hMdim : (Module.finrank 𝕜 M : ℤ) = boxCount B J T Θ := by
    have h := finrank_restrictSupport_finset (K := 𝕜) hI.toFinset
    rw [Set.Finite.coe_toFinset] at h
    change (Module.finrank 𝕜 (restrictSupport 𝕜 (taperBox B J T Θ)) : ℤ) = _
    rw [h]
    exact taperBox_card B J T Θ
  let mulf : R →ₗ[𝕜] R := LinearMap.mulLeft 𝕜 f
  let G : Submodule 𝕜 R := M.comap mulf
  have hGdim : ∃ _ : Module.Finite 𝕜 G,
      (Module.finrank 𝕜 G : ℤ) ≤ varMult bl jl tl L B J T Θ := by
    by_cases hguard : bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ
    · let Nset := taperBox (B - bl) (J - jl) (T - tl) (Θ - L)
      have hN := taperBox_finite (B - bl) (J - jl) (T - tl) (Θ - L)
      have : Module.Finite 𝕜 (restrictSupport 𝕜 Nset) := restrictSupport_finite hN
      have hle : G ≤ restrictSupport 𝕜 Nset := by
        intro g hg
        by_cases hg0 : g = 0
        · rw [hg0]; exact Submodule.zero_mem _
        · exact (cofactor_mem_var f hf bl jl tl L hbl hjl htl hL hg0 hg).2
      have : Module.Finite 𝕜 G := Submodule.finiteDimensional_of_le hle
      refine ⟨inferInstance, ?_⟩
      have h1 := Submodule.finrank_mono hle
      have h2 := finrank_restrictSupport_finset (K := 𝕜) hN.toFinset
      rw [Set.Finite.coe_toFinset] at h2
      have h3 := taperBox_card (B - bl) (J - jl) (T - tl) (Θ - L)
      have h4 : varMult bl jl tl L B J T Θ = boxCount (B - bl) (J - jl) (T - tl) (Θ - L) := by
        unfold varMult
        rw [if_pos hguard]
      rw [h4, ← h3]
      change Module.finrank 𝕜 G ≤ Module.finrank 𝕜 (restrictSupport 𝕜 Nset) at h1
      rw [h2] at h1
      exact_mod_cast h1
    · have hbot : G = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        by_contra hg0
        exact hguard (cofactor_mem_var f hf bl jl tl L hbl hjl htl hL hg0 hg).1
      rw [hbot]
      refine ⟨inferInstance, ?_⟩
      have h4 : varMult bl jl tl L B J T Θ = 0 := by
        unfold varMult
        rw [if_neg hguard]
      rw [h4, finrank_bot]
      rfl
  obtain ⟨hGfin, hGle⟩ := hGdim
  have := hGfin
  let Mf : Submodule 𝕜 R := G.map mulf
  have hMfle : Module.finrank 𝕜 Mf ≤ Module.finrank 𝕜 G := Submodule.finrank_map_le mulf G
  let p : Submodule 𝕜 M := Mf.comap M.subtype
  obtain ⟨q, hq⟩ := p.exists_isCompl
  have hpq := Submodule.finrank_add_eq_of_isCompl hq
  have hp_le : Module.finrank 𝕜 p ≤ Module.finrank 𝕜 Mf := by
    have h1 : p.map M.subtype ≤ Mf := Submodule.map_comap_le _ _
    have h2 := Submodule.finrank_mono h1
    rwa [Submodule.finrank_map_subtype_eq] at h2
  let C : Submodule 𝕜 R := q.map M.subtype
  have hCdim : Module.finrank 𝕜 C = Module.finrank 𝕜 q := Submodule.finrank_map_subtype_eq M q
  have hCM : C ≤ M := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  refine ⟨C, Submodule.finiteDimensional_of_le hCM, ?_, ?_, ?_, ?_⟩
  · have hd : varDepthDim bl bh jl jh tl L H a (some (B, J, T)) =
        max 0 (boxCount B J T Θ - varMult bl jl tl L B J T Θ) := by
      simp only [varDepthDim]
      rw [if_pos ⟨hB, hJ, hΘa⟩]
    rw [hd, hCdim]
    apply max_le (by positivity)
    have : (Module.finrank 𝕜 M : ℤ) = Module.finrank 𝕜 p + Module.finrank 𝕜 q := by
      exact_mod_cast hpq.symm
    have h5 : (Module.finrank 𝕜 p : ℤ) ≤ Module.finrank 𝕜 G := by exact_mod_cast hp_le.trans hMfle
    linarith
  · rintro _ ⟨y, hy, rfl⟩ ⟨g, hg⟩
    have hyM : (y : R) ∈ M := y.2
    have hgG : g ∈ G := by
      change f * g ∈ M
      rw [← hg]
      exact hyM
    have hyp : y ∈ p := by
      change (y : R) ∈ Mf
      exact ⟨g, hgG, hg.symm⟩
    have hy0 : y = 0 := by
      have := hq.disjoint.le_bot ⟨hyp, hy⟩
      exact (Submodule.mem_bot 𝕜).mp this
    rw [hy0]
    rfl
  · intro c hc
    exact pow_mul_mem_source_var f hf bh jh H hbh hjh hH hB hJ hΘa (hCM hc)
  · intro c hc _
    exact ⟨B, J, T, rfl, ⟨hB, hJ, hΘa⟩, hCM hc⟩
theorem exists_varFadicSpace (f : R) (hf : f ≠ 0) (bl bh jl jh tl L H : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (htl : tl ≤ f.weightedTotalDegree topWeight)
    (hL : L ≤ f.weightedTotalDegree taperWeight) (hH : f.weightedTotalDegree taperWeight ≤ H)
    (n : ℕ) (box : ℕ → Entry) :
    ∃ U : Submodule 𝕜 R,
      U ≤ restrictSupport 𝕜 jetExponents ∧
      varFadicDim bl bh jl jh tl L H n box ≤ (Module.finrank 𝕜 U : ℤ) ∧
      ∀ v ∈ U, v ≠ 0 → ∃ (a B J T : ℕ) (c h : R),
        a < n ∧ box a = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
        v = f ^ a * (c + f * h) ∧ c ≠ 0 ∧ ¬ f ∣ c ∧
        c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a)) := by
  classical
  choose C hCfin hCdim hCdvd hCsrc hCbox using
    fun a => exists_varDepthSpace f hf bl bh jl jh tl L H hbl hbh hjl hjh htl hL hH a (box a)
  have : ∀ i : Fin n, FiniteDimensional 𝕜 (C i) := fun i => hCfin i
  let Φ : (∀ i : Fin n, C i) →ₗ[𝕜] R :=
    ∑ i : Fin n, (LinearMap.mulLeft 𝕜 (f ^ (i : ℕ))).comp ((C i).subtype.comp (LinearMap.proj i))
  have hΦ (w : ∀ i : Fin n, C i) : Φ w = ∑ i : Fin n, f ^ (i : ℕ) * (w i : R) := by
    simp [Φ, LinearMap.sum_apply]
  let seq (w : ∀ i : Fin n, C i) : ℕ → R := fun i => if h : i < n then (w ⟨i, h⟩ : R) else 0
  have hseq (w : ∀ i : Fin n, C i) : Φ w = ∑ i ∈ range n, f ^ i * seq w i := by
    rw [hΦ, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [seq, i.isLt]
  have hseqC (w : ∀ i : Fin n, C i) (i : ℕ) (hi : i < n) : seq w i = (w ⟨i, hi⟩ : R) := by
    simp [seq, hi]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [hseq] at hw
    have hall := fadic_zero f hf n (seq w) (fun i hi hdiv => by
      rw [hseqC w i hi] at hdiv ⊢
      exact hCdvd i _ (w ⟨i, hi⟩).2 hdiv) hw
    funext i
    have := hall i i.isLt
    rw [hseqC w i i.isLt] at this
    exact Subtype.ext this
  refine ⟨LinearMap.range Φ, ?_, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [hΦ]
    exact Submodule.sum_mem _ fun i _ => hCsrc i _ (w i).2
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    unfold varFadicDim
    rw [← Fin.sum_univ_eq_sum_range (fun a => varDepthDim bl bh jl jh tl L H a (box a)) n,
      Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hCdim i
  · rintro _ ⟨w, rfl⟩ hv
    have hex : ∃ i, i < n ∧ seq w i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hv
      rw [hseq]
      exact Finset.sum_eq_zero fun i hi => by
        rw [hnone i (Finset.mem_range.mp hi), mul_zero]
    let a := Nat.find hex
    obtain ⟨han, hane⟩ := Nat.find_spec hex
    have hlow : ∀ i < a, seq w i = 0 := by
      intro i hi
      by_contra hne
      exact Nat.find_min hex hi ⟨hi.trans han, hne⟩
    obtain ⟨h, hh⟩ := fadic_shape f a n (seq w) han hlow
    have hcC : seq w a ∈ C a := by
      rw [hseqC w a han]
      exact (w ⟨a, han⟩).2
    obtain ⟨B, J, T, hbox, hok, hmem⟩ := hCbox a _ hcC hane
    refine ⟨a, B, J, T, seq w a, h, han, hbox, hok, ?_, hane, ?_, hmem⟩
    · rw [← hh, ← hseq]
    · intro hdvd
      exact hane (hCdvd a _ hcC hdvd)
def varPlainDim (B J T : ℕ) : ℤ := boxCount (min B 4012) (min J 1650) T 131312
def varGateDim (S : ℤ) (bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ) (n : ℕ → ℕ)
    (box : ℕ → ℕ → Entry) (r : ℕ) : ℤ :=
  if Rt ≤ r then S
  else max (varPlainDim (plain r).1 (plain r).2.1 (plain r).2.2)
    (varFadicDim bl bh jl jh tl L H (n r) (box r))
theorem exists_varGateSpace (f : R) (hf : f ≠ 0) (bl bh jl jh tl L H : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (htl : tl ≤ f.weightedTotalDegree topWeight)
    (hL : L ≤ f.weightedTotalDegree taperWeight) (hH : f.weightedTotalDegree taperWeight ≤ H)
    (Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ) (n : ℕ → ℕ) (box : ℕ → ℕ → Entry) (r : ℕ) :
    ∃ U : Submodule 𝕜 R,
      U ≤ restrictSupport 𝕜 jetExponents ∧
      varGateDim (jetColumns.card : ℤ) bl bh jl jh tl L H Rt plain n box r ≤
        (Module.finrank 𝕜 U : ℤ) ∧
      ∀ v ∈ U, v ≠ 0 →
        Rt ≤ r ∨
        v ∈ restrictSupport 𝕜
          (taperBox (min (plain r).1 4012) (min (plain r).2.1 1650) (plain r).2.2 131312) ∨
        ∃ (a B J T : ℕ) (c h : R),
          a < n r ∧ box r a = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
          v = f ^ a * (c + f * h) ∧ c ≠ 0 ∧ ¬ f ∣ c ∧
          c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a)) := by
  classical
  by_cases hterm : Rt ≤ r
  · refine ⟨restrictSupport 𝕜 jetExponents, le_rfl, ?_, fun _ _ _ => Or.inl hterm⟩
    have h := finrank_restrictSupport_finset (K := 𝕜) jetColumns
    have hset : (jetColumns : Set JetExp) = jetExponents := Set.Finite.coe_toFinset _
    rw [hset] at h
    unfold varGateDim
    rw [if_pos hterm, h]
  · by_cases hcmp : varFadicDim bl bh jl jh tl L H (n r) (box r) ≤
        varPlainDim (plain r).1 (plain r).2.1 (plain r).2.2
    · set B := min (plain r).1 4012
      set J := min (plain r).2.1 1650
      have hfin := taperBox_finite B J (plain r).2.2 131312
      refine ⟨restrictSupport 𝕜 (taperBox B J (plain r).2.2 131312),
        restrictSupport_mono 𝕜 (taperBox_subset_source (min_le_right _ _) (min_le_right _ _)),
        ?_, fun v hv _ => Or.inr (Or.inl hv)⟩
      have h := finrank_restrictSupport_finset (K := 𝕜) hfin.toFinset
      rw [Set.Finite.coe_toFinset] at h
      unfold varGateDim
      rw [if_neg hterm, max_eq_left hcmp, h]
      exact (taperBox_card B J (plain r).2.2 131312).ge
    · obtain ⟨U, hU, hdim, hrow⟩ :=
        exists_varFadicSpace f hf bl bh jl jh tl L H hbl hbh hjl hjh htl hL hH (n r) (box r)
      refine ⟨U, hU, ?_, fun v hv hne => Or.inr (Or.inr (hrow v hv hne))⟩
      unfold varGateDim
      rw [if_neg hterm, max_eq_right (le_of_not_ge hcmp)]
      exact hdim
end Field
end FadicGate

end Merged_FadicVar

-- merged module FadicDegree
section Merged_FadicDegree
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open MvPolynomial
open scoped BigOperators
variable {R : Type*} [CommSemiring R]
theorem wdeg_top_eq_degreeOf (g : MvPolynomial (Fin 4) R) :
    g.weightedTotalDegree topWeight = g.degreeOf 3 := by
  rw [degreeOf_eq_sup]
  unfold weightedTotalDegree
  exact Finset.sup_congr rfl fun m _ => w_top m
theorem taper_ge_grade (g : MvPolynomial (Fin 4) R) :
    26 * g.weightedTotalDegree gradeWeight ≤ g.weightedTotalDegree taperWeight := by
  classical
  rcases g.support.eq_empty_or_nonempty with he | hne
  · simp [weightedTotalDegree, he]
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup g.support hne
      (fun s => Finsupp.weight gradeWeight s)
    have h1 : g.weightedTotalDegree gradeWeight = Finsupp.weight gradeWeight m := hmax
    have h2 := le_weightedTotalDegree taperWeight hm
    rw [w_taper'] at h2
    rw [h1]
    omega
theorem taper_le (g : MvPolynomial (Fin 4) R) (b j K : ℕ)
    (hb : ∀ m ∈ g.support, Finsupp.weight gradeWeight m ≤ b)
    (hj : ∀ m ∈ g.support, Finsupp.weight oldWeight m ≤ j)
    (hK : ∀ m ∈ g.support, m 0 + 2 * m 1 + 2 * m 2 + 2 * m 3 ≤ K) :
    g.weightedTotalDegree taperWeight ≤ min (26 * b + 25 * j) (b + 25 * K) := by
  unfold weightedTotalDegree
  apply Finset.sup_le
  intro m hm
  have h1 := hb m hm
  have h2 := hj m hm
  have h3 := hK m hm
  rw [w_grade] at h1
  rw [w_old] at h2
  rw [w_taper]
  apply le_min <;> omega
end FadicGate

end Merged_FadicDegree

end Merged_FadicDegree

-- merged module FadicChunk
section Merged_FadicChunk
set_option Elab.async false
set_option autoImplicit false
namespace FadicGate
open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns cumulativeExponents
  mem_cumulativeColumns)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
theorem cappedCount_nonneg (d u t : ℤ) : 0 ≤ cappedCount d u t := by
  rw [← capped_card K1_13_2_2_2.proof]
  positivity
theorem cappedCount_mono {d d' : ℕ} (hd : d ≤ d') (u t : ℤ) :
    cappedCount d u t ≤ cappedCount d' u t := by
  rw [← capped_card K1_13_2_2_2.proof, ← capped_card K1_13_2_2_2.proof]
  have hcard : (cappedColumns d u t).card ≤ (cappedColumns d' u t).card := by
    let shift : JetExp → JetExp := fun e => e + Finsupp.single 0 (d' - d)
    apply Finset.card_le_card_of_injOn shift
    · intro e he
      obtain ⟨hj, ht⟩ := mem_cappedColumns.mp he
      obtain ⟨hg, hi⟩ := mem_cumulativeColumns.mp hj
      have hg' : ((Finsupp.weight gradeWeight e : ℕ) : ℤ) = (d : ℤ) := hg
      have hi' : ((Finsupp.weight oldWeight e : ℕ) : ℤ) ≤ u := hi
      apply mem_cappedColumns.mpr
      have e0 : shift e 0 = e 0 + (d' - d) := by simp [shift]
      have e1 : shift e 1 = e 1 := by simp [shift]
      have e2 : shift e 2 = e 2 := by simp [shift]
      have e3 : shift e 3 = e 3 := by simp [shift]
      refine ⟨mem_cumulativeColumns.mpr ⟨?_, ?_⟩, ?_⟩
      · change ((Finsupp.weight gradeWeight (shift e) : ℕ) : ℤ) = (d' : ℤ)
        rw [w_grade, e0, e1, e2, e3]
        rw [w_grade] at hg'
        push_cast at hg' ⊢
        omega
      · change ((Finsupp.weight oldWeight (shift e) : ℕ) : ℤ) ≤ u
        rw [w_old, e1, e2, e3, ← w_old]
        exact hi'
      · change ((shift e 3 : ℕ) : ℤ) ≤ t
        rw [e3]
        exact ht
    · intro x _ y _ hxy
      exact add_right_cancel hxy
  exact_mod_cast hcard
theorem padGrade_ge {Θ lo q hi : ℕ} (hlo : lo ≤ q) (hhi : q ≤ hi) :
    min lo ((Θ - 26 * hi) / 25) ≤ padGrade Θ q := by
  unfold padGrade
  apply le_min
  · exact (min_le_left _ _).trans hlo
  · exact (min_le_right _ _).trans (Nat.div_le_div_right (by omega))
theorem padGrade_le {Θ lo q hi : ℕ} (hlo : lo ≤ q) (hhi : q ≤ hi) :
    padGrade Θ q ≤ min hi ((Θ - 26 * lo) / 25) := by
  unfold padGrade
  exact min_le_min hhi (Nat.div_le_div_right (by omega))
theorem term_nonneg (J T Θ q : ℕ) : 0 ≤ term J T Θ q := by
  unfold term
  split
  · exact cappedCount_nonneg _ _ _
  · exact le_rfl
def segLo (base h k : ℕ) : ℕ := base + h * k
def segHi (base h m k : ℕ) : ℕ := base + min (h * k + h - 1) (m - 1)
def lowDeg (Θ base h m k : ℕ) : ℕ := min (segLo base h k) ((Θ - 26 * segHi base h m k) / 25)
def highDeg (Θ base h m k : ℕ) : ℕ := min (segHi base h m k) ((Θ - 26 * segLo base h k) / 25)
def lowSeg (J T Θ base h m k : ℕ) : ℤ :=
  if 26 * segHi base h m k ≤ Θ then cappedCount (lowDeg Θ base h m k : ℕ) J T else 0
def highSeg (J T Θ base h m k : ℕ) : ℤ :=
  if 26 * segLo base h k ≤ Θ then cappedCount (highDeg Θ base h m k : ℕ) J T else 0
theorem seg_bounds {base h m i : ℕ} (hh : 0 < h) (hi : i < m) :
    segLo base h (i / h) ≤ base + i ∧ base + i ≤ segHi base h m (i / h) := by
  have h1 : h * (i / h) ≤ i := Nat.mul_div_le i h
  have h2 : i % h < h := Nat.mod_lt i hh
  have h3 : i % h + h * (i / h) = i := Nat.mod_add_div i h
  unfold segLo segHi
  constructor
  · omega
  · have : i ≤ h * (i / h) + h - 1 := by omega
    have : i ≤ m - 1 := by omega
    omega
theorem term_of_le {J T Θ q : ℕ} (hq : 26 * q ≤ Θ) :
    term J T Θ q = cappedCount (padGrade Θ q : ℕ) J T := by
  unfold term
  exact if_pos hq
theorem term_of_gt {J T Θ q : ℕ} (hq : ¬ 26 * q ≤ Θ) : term J T Θ q = 0 := by
  unfold term
  exact if_neg hq
theorem lowSeg_le {J T Θ base h m i : ℕ} (hh : 0 < h) (hi : i < m) :
    lowSeg J T Θ base h m (i / h) ≤ term J T Θ (base + i) := by
  obtain ⟨hlo, hhi⟩ := seg_bounds (base := base) (m := m) hh hi
  set lo := segLo base h (i / h)
  set hi' := segHi base h m (i / h)
  by_cases h26 : 26 * hi' ≤ Θ
  · have hq : 26 * (base + i) ≤ Θ := le_trans (Nat.mul_le_mul_left 26 hhi) h26
    have hl : lowSeg J T Θ base h m (i / h) = cappedCount (lowDeg Θ base h m (i / h) : ℕ) J T := by
      unfold lowSeg
      exact if_pos h26
    rw [hl, term_of_le hq]
    exact cappedCount_mono (padGrade_ge hlo hhi) (J : ℤ) (T : ℤ)
  · have hl : lowSeg J T Θ base h m (i / h) = 0 := by
      unfold lowSeg
      exact if_neg h26
    rw [hl]
    exact term_nonneg _ _ _ _
theorem le_highSeg {J T Θ base h m i : ℕ} (hh : 0 < h) (hi : i < m) :
    term J T Θ (base + i) ≤ highSeg J T Θ base h m (i / h) := by
  obtain ⟨hlo, hhi⟩ := seg_bounds (base := base) (m := m) hh hi
  set lo := segLo base h (i / h)
  set hi' := segHi base h m (i / h)
  by_cases h26 : 26 * lo ≤ Θ
  · have hl : highSeg J T Θ base h m (i / h) =
        cappedCount (min hi' ((Θ - 26 * lo) / 25) : ℕ) J T := by
      unfold highSeg
      exact if_pos h26
    rw [hl]
    by_cases hq : 26 * (base + i) ≤ Θ
    · rw [term_of_le hq]
      exact cappedCount_mono (padGrade_le hlo hhi) (J : ℤ) (T : ℤ)
    · rw [term_of_gt hq]
      exact cappedCount_nonneg _ _ _
  · have hq : ¬ 26 * (base + i) ≤ Θ := fun hq => h26 (le_trans (Nat.mul_le_mul_left 26 hlo) hq)
    have hl : highSeg J T Θ base h m (i / h) = 0 := by
      unfold highSeg
      exact if_neg h26
    rw [hl, term_of_gt hq]
theorem sum_div_block (F : ℕ → ℤ) {h : ℕ} (hh : 0 < h) (n : ℕ) :
    ∑ i ∈ range n, F (i / h) = h * ∑ k ∈ range (n / h), F k + ((n % h : ℕ) : ℤ) * F (n / h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have e1 := Nat.mod_add_div n h
    have e2 := Nat.mod_lt n hh
    rcases Nat.lt_or_ge (n % h + 1) h with hlt | hge
    · have hq : (n + 1) / h = n / h ∧ (n + 1) % h = n % h + 1 :=
        (Nat.div_mod_unique hh).mpr ⟨by omega, hlt⟩
      rw [hq.1, hq.2]
      push_cast
      ring
    · have hq : (n + 1) / h = n / h + 1 ∧ (n + 1) % h = 0 := by
        apply (Nat.div_mod_unique hh).mpr
        refine ⟨?_, hh⟩
        rw [Nat.mul_succ]
        omega
      have hr : n % h = h - 1 := by omega
      rw [hq.1, hq.2, sum_range_succ, hr]
      have hh1 : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [hh1]
      push_cast
      ring
def segSumLow (J T Θ base h m : ℕ) : ℤ :=
  h * ∑ k ∈ range (m / h), lowSeg J T Θ base h m k +
    ((m % h : ℕ) : ℤ) * lowSeg J T Θ base h m (m / h)
def segSumHigh (J T Θ base h m : ℕ) : ℤ :=
  h * ∑ k ∈ range (m / h), highSeg J T Θ base h m k +
    ((m % h : ℕ) : ℤ) * highSeg J T Θ base h m (m / h)
theorem segSumLow_le {J T Θ base h m : ℕ} (hh : 0 < h) :
    segSumLow J T Θ base h m ≤ ∑ i ∈ range m, term J T Θ (base + i) := by
  unfold segSumLow
  rw [← sum_div_block (lowSeg J T Θ base h m) hh m]
  exact sum_le_sum fun i hi => lowSeg_le hh (mem_range.mp hi)
theorem le_segSumHigh {J T Θ base h m : ℕ} (hh : 0 < h) :
    ∑ i ∈ range m, term J T Θ (base + i) ≤ segSumHigh J T Θ base h m := by
  unfold segSumHigh
  rw [← sum_div_block (highSeg J T Θ base h m) hh m]
  exact sum_le_sum fun i hi => le_highSeg hh (mem_range.mp hi)
def fastLow (B J T Θ h : ℕ) : ℤ :=
  segSumLow J T Θ 0 h (flatLo B J) +
    ((flatHi B J Θ - flatLo B J : ℕ) : ℤ) * cappedCount J J T +
    segSumLow J T Θ (flatHi B J Θ) h (B + 1 - flatHi B J Θ)
def fastHigh (B J T Θ h : ℕ) : ℤ :=
  segSumHigh J T Θ 0 h (flatLo B J) +
    ((flatHi B J Θ - flatLo B J : ℕ) : ℤ) * cappedCount J J T +
    segSumHigh J T Θ (flatHi B J Θ) h (B + 1 - flatHi B J Θ)
theorem fastLow_le (B J T Θ : ℕ) {h : ℕ} (hh : 0 < h) : fastLow B J T Θ h ≤ boxCount B J T Θ := by
  rw [← fastCount_eq]
  unfold fastLow fastCount
  rw [intPrefix_eq, intPrefix_eq]
  have h1 := segSumLow_le (J := J) (T := T) (Θ := Θ) (base := 0) (m := flatLo B J) hh
  have h2 := segSumLow_le (J := J) (T := T) (Θ := Θ) (base := flatHi B J Θ)
    (m := B + 1 - flatHi B J Θ) hh
  simp only [zero_add] at h1
  linarith
theorem le_fastHigh (B J T Θ : ℕ) {h : ℕ} (hh : 0 < h) : boxCount B J T Θ ≤ fastHigh B J T Θ h := by
  rw [← fastCount_eq]
  unfold fastHigh fastCount
  rw [intPrefix_eq, intPrefix_eq]
  have h1 := le_segSumHigh (J := J) (T := T) (Θ := Θ) (base := 0) (m := flatLo B J) hh
  have h2 := le_segSumHigh (J := J) (T := T) (Θ := Θ) (base := flatHi B J Θ)
    (m := B + 1 - flatHi B J Θ) hh
  simp only [zero_add] at h1
  linarith
end FadicGate

end Merged_FadicChunk

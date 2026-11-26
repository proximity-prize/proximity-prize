import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZCUPQZb
import ProximityPrize.SubmissionLower.Fat6966Bank24000
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.UpperBranch5

section Merged6967_FadicChunk
set_option Elab.async false


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
#print axioms FadicGate.taperBox_card
#print axioms FadicGate.fastCount_eq

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
#print axioms FadicGate.pow_mul_mem_source_var
#print axioms FadicGate.cofactor_mem_var
#print axioms FadicGate.exists_varFadicSpace
#print axioms FadicGate.exists_varGateSpace

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
#print axioms FadicGate.wdeg_top_eq_degreeOf
#print axioms FadicGate.taper_ge_grade
#print axioms FadicGate.taper_le

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
#print axioms FadicGate.cappedCount_mono
#print axioms FadicGate.sum_div_block
#print axioms FadicGate.fastLow_le
#print axioms FadicGate.le_fastHigh

end Merged_FadicChunk

end Merged6967_FadicChunk

section Merged6967_Fat6966Chart
set_option Elab.async false



set_option Elab.async false
set_option maxHeartbeats 1000000
/-! Low-specific chart for the isolated-point bound: copy of `Fast056`/`Fast062` chart machinery
with the new resultant box (367,443,0, 124,200,0). -/
section
set_option autoImplicit false
namespace Low6966FatChart
noncomputable section
open K1_13 K1_13_7 MvPolynomial
open scoped Pointwise
open K1_13_7_6 (cap chartDegree zeroPrime chartDegree_eq_one cap_ncard)
open K1_13_7_6 (cap_add_subset nsmul_cap_subset indexWeight_eq zero_mem_cap)
abbrev totalCap : ℕ := 380928000
abbrev halfIndexCap : ℕ := 64400000
abbrev chartExponents := cap totalCap (2 * halfIndexCap)
abbrev chartMap := monomialMap GeometricX chartExponents
theorem chartMap_surjective : Function.Surjective chartMap := by
  apply monomialMap_surjective
  intro i
  change (Finsupp.single i 1).degree ≤ totalCap ∧
    Finsupp.single i 1 1 + 2 * Finsupp.single i 1 2 ≤ 2 * halfIndexCap
  fin_cases i <;> norm_num [Finsupp.degree_single, Finsupp.single_apply, totalCap, halfIndexCap]
private theorem genericRow_mem_chart (P : Row 3) (hP : LowerCaps P totalCap (2 * halfIndexCap)) :
    genericRow P ∈ restrictSupport GeometricX chartExponents := by
  intro e he
  have he' : e ∈ P.support := support_map_subset _ _ he
  refine ⟨(le_totalDegree he').trans hP.1, ?_⟩
  rw [← indexWeight_eq]
  exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum fun i a => i.val * a) he').trans hP.2
theorem chart_lift (P : Row 3) (hP : LowerCaps P totalCap (2 * halfIndexCap)) :
    ∃ L : MvPolynomial chartExponents GeometricX,
      chartMap L = genericRow P ∧ L.totalDegree ≤ 1 := by
  let h := genericRow_mem_chart P hP
  exact ⟨monomialLift (genericRow P) h, monomialMap_monomialLift (genericRow P) h,
    totalDegree_monomialLift_le_one (genericRow P) h⟩
private theorem chartHilbert_le (n : ℕ) :
    affineHilbertFunction (RingHom.ker chartMap) n ≤
      (cap (totalCap * n) ((2 * halfIndexCap) * n)).ncard := by
  let S := cap (totalCap * n) ((2 * halfIndexCap) * n)
  let M := restrictSupport GeometricX S
  let : Module.Finite GeometricX M := restrictSupport_finite (Set.toFinite S)
  have hmap (L : MvPolynomial chartExponents GeometricX) (hL : L.totalDegree ≤ n) :
      chartMap L ∈ M :=
    restrictSupport_mono GeometricX (nsmul_cap_subset _ _ n)
      (monomialMap_mem_restrictSupport_nsmul (zero_mem_cap _ _) hL)
  calc
    affineHilbertFunction (RingHom.ker chartMap) n ≤
        Module.finrank GeometricX (M.map (Ideal.Quotient.mkₐ GeometricX ⊥).toLinearMap) := by
      rw [RingHom.ker_eq_comap_bot]
      exact affineHilbertFunction_comap_le_finrank_map chartMap ⊥ M hmap
    _ ≤ Module.finrank GeometricX M := Submodule.finrank_map_le _ _
    _ = S.ncard := by
      rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeometricX S), Nat.card_coe_set_eq]
theorem chartDegree_bound :
    chartDegree chartMap zeroPrime ≤ 6 * (halfIndexCap : ℚ) ^ 2 * (totalCap - halfIndexCap : ℚ) := by
  let a : ℚ := halfIndexCap
  let b : ℚ := totalCap - halfIndexCap
  let H : Polynomial ℚ := Polynomial.C (a ^ 2 * b) * Polynomial.X ^ 3 +
    Polynomial.C (a ^ 2 + 2 * a * b) * Polynomial.X ^ 2 +
    Polynomial.C (2 * a + b) * Polynomial.X ^ 1 + Polynomial.C 1
  have hdim : (affineHilbertPolynomial (RingHom.ker chartMap)).natDegree = 3 := by
    rw [natDegree_affineHilbertPolynomial_ker_of_surjective chartMap chartMap_surjective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hH : H.natDegree ≤ 3 := by
    dsimp only [H]
    apply Polynomial.natDegree_add_le_of_degree_le _ (by simp)
    apply Polynomial.natDegree_add_le_of_degree_le _
      ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by decide))
    apply Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_C_mul_X_pow_le _ _)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by decide)
  have hB : ∀ n : ℕ, 2 * (halfIndexCap * n) ≤ totalCap * n := fun n => by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right n (by decide)
  have hfit : ∀ n : ℕ, (affineHilbertFunction (RingHom.ker chartMap) n : ℚ) ≤ H.eval (n : ℚ) := by
    intro n
    have h := chartHilbert_le n
    rw [Nat.mul_assoc, cap_ncard _ _ (hB n)] at h
    refine (Nat.cast_le.mpr h).trans_eq ?_
    have hsub : halfIndexCap * n ≤ totalCap * n + 1 := by have := hB n; omega
    push_cast [Nat.cast_sub hsub]
    simp only [H, a, b, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  change affineDegree ((⊥ : Ideal Lower).comap chartMap) ≤ _
  rw [← RingHom.ker_eq_comap_bot]
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim hH
    (Filter.Eventually.of_forall hfit)).trans_eq ?_
  norm_num [H, a, b, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one]
abbrev resultantBox : Shape := Low6966Fat.resultantBox
open K1_13_7_5 K1_13_7_6
theorem supported_resultant {P : Row 3} (hP : LowerCaps P resultantBox.b resultantBox.j) :
    Supported resultantBox (liftRow P) := by
  classical
  intro m hm
  change m ∈ (MvPolynomial.rename Fin.castSucc (genericRow P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 3), Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : n ∈ P.support := MvPolynomial.support_map_subset genericCoeff P hn
  refine ⟨?_, ?_, ?_⟩
  · rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact (MvPolynomial.le_totalDegree hn').trans hP.1
  · rw [Finsupp.sum_mapDomain_index (fun _ => Nat.mul_zero _) (fun _ _ _ => Nat.mul_add ..)]
    exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum (fun i a => i.val * a)) hn').trans hP.2
  · have hlast : (3 : Fin 4) ∉ Set.range (@Fin.castSucc 3) := by
      rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last i hi
    exact (Finsupp.mapDomain_of_notMem_range n _ hlast).le
end
end Low6966FatChart
end

end Merged6967_Fat6966Chart

section Merged6967_Fat6966Contacts
set_option Elab.async false


set_option Elab.async false
section
namespace Low6966FatContacts
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open P0_9_4 (line eval_line coeff_contact order_of_locator_lines translate_map)
set_option maxRecDepth 12000
private def Bounded (F : Polynomial (Polynomial Geom)) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 48690 * j
private theorem bounded_mul {F G : Polynomial (Polynomial Geom)} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : (Polynomial Geom)) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial (Polynomial Geom)) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial (Polynomial Geom)} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (Q : Row 3) (T U : (Polynomial Geom)) (t : ℕ)
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 179761)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 48690 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial (Polynomial Geom) :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 48690 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 179761 - i.val ≤ (131071 - i.val) + 48690
      omega
    change ((F i).coeff k).natDegree ≤ b i + 48690 * k
    rw [show F i = _ from rfl, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using ht
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hterm := bounded_mul (bounded_C (Q.coeff a) le_rfl)
    (bounded_prod a.support (fun i => F i ^ a i) (fun i => b i * a i)
      (fun i _ => bounded_pow (hF i) (a i))) j
  exact hterm.trans (Nat.add_le_add_right (hQ a ha) _)
private theorem line_coeff_zero (w : I → K) (H res T : (Polynomial Geom)) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 179759)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : (Polynomial Geom)) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 48690 * j < r * 179759) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 179761 :=
    natDegree_mul_le.trans (by rw [locator_natDegree, hA]; omega)
  have hc (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ r ∣ (line Q T U).eval (C c) := by
    rw [eval_line]
    apply hcontact i
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    have ht : (T + c • U).eval (x i) = T.eval (x i) := by simp [eval_smul, hU0]
    change (H * (T + c • U) + res).eval (x i) = _
    rw [eval_add, eval_mul, ht, ← eval_mul, ← eval_add]
    exact hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  apply K1_11.eq_zero_of_many_contacts A x hx r
  · exact fun i hi => coeff_contact _ _ _ (hc i hi) j
  · rw [hA]
    exact (line_degree Q T U t hQ hT hU j).trans_lt hj
theorem raw_locator_order (w : I → K) (H res T : (Polynomial Geom)) (t k : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071)
    (hhits : ∃ A : Finset I, 179759 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (hc : RawContact 5000 w H res Q) (hQ : RawCut t Q)
    (hcut : t + 48690 * k < 5000 * 179759) :
    LowerOrder (MvPolynomial.map inclX Q) (trajectory T) (k + 1) := by
  obtain ⟨B, hB, hhits⟩ := hhits
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq hB
  let x (i : I) := embed (node i)
  have ho : OrderAt Q T (k + 1) := by
    apply order_of_locator_lines Q T (locator x A) (locator_monic x A).ne_zero
    intro V hV j hj
    exact line_coeff_zero w H res T t 5000 Q hT hQ hc A hA
      (fun i hi => hhits i (hAB hi)) V hV j (by omega)
  intro a
  rw [translate_map]
  intro ha
  exact ho a (MvPolynomial.support_map_subset _ _ ha)
end
end Low6966FatContacts
end
section
namespace Low6966FatContacts
noncomputable section
open K1 K1_13 K1_13_4_3 Low6966Fat
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open K1_13_4_3_1 (coeff_scalar support_seed weight_shift)
open K1_13_4_3 (coeff_eq_zero_of_lowerOrder)
private theorem trueCut_seed (H : (Polynomial Geom)) (i t : ℕ) (F : PhysicalRow)
    (hH : H.natDegree ≤ 2316) (hF : TrueCut H.natDegree t F) :
    TrueCut H.natDegree (t + 6948 * i) (clearedSeed H i F) := by
  intro b hb
  obtain ⟨u, hu⟩ := coeff_scalar F i b
  have hbefore := hF _ (support_seed hb)
  let w : SeedVar → ℕ := fun j => j.elim 0 (fun k => 131071 + H.natDegree - k.val)
  have hw (a : SeedVar →₀ ℕ) :
      a.sum (fun j e => j.elim 0 (fun k => (131071 + H.natDegree - k.val) * e)) =
        Finsupp.weight w a := by
    rw [Finsupp.weight_apply]
    congr 1
    funext j e
    cases j <;> simp [w, Nat.mul_comm]
  rw [hw, weight_shift w rfl] at hbefore
  rw [hw]
  have hcoeff : ((clearedSeed H i F).coeff b).natDegree ≤
      (H ^ (3 * i)).natDegree + (F.coeff (Finsupp.single none i + b)).natDegree := by
    simp only [clearedSeed, ← partial_eq_mixedHasse, MvPolynomial.coeff_C_mul, hu]
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add_left (Polynomial.natDegree_mul_C_le _ _) _)
  have hp' : (H ^ (3 * i)).natDegree ≤ 6948 * i := by
    calc
      _ ≤ (3 * i) * H.natDegree := Polynomial.natDegree_pow_le
      _ ≤ (3 * i) * 2316 := Nat.mul_le_mul_left _ hH
      _ = 6948 * i := by ring
  omega
private theorem seed_motion (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hh : P.H.natDegree ≤ 2316) (box : Shape) (t : ℕ) (F : PhysicalRow)
    (hF : Source w P L box t F) (i : ℕ) :
    Source w P L box (t + 6948 * i) (clearedSeed P.H i F) := by
  obtain ⟨hcap, hcut, hcontact, hpole⟩ := hF
  refine ⟨K1_13_4_3_1.caps_seed P.H i F box hcap, ?_, K1_13_4_3_1.contact_seed P.H i w F hcontact,
    K1_13_4_3_1.pole_seed P L _ i F hpole⟩
  simpa only [Nat.add_right_comm] using trueCut_seed P.H i _ F hh hcut
private theorem mixedOrder_iff_coeff {F : GenericRow} {z : GenericX}
    {y : Fin 3 → GenericX} {d : ℕ} :
    MixedOrder F z y d ↔
      ∀ a, mixedWeight a < d → (K1_13_4.translate (atPoint z y) F).coeff a = 0 := by
  constructor
  · intro h a ha
    by_contra hz
    exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
  · intro h a ha
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hlt)
private theorem fixed_seed_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : Low6966Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 48690 * k < 5000 * 179759) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 179759 ≤ B.card ∧
      ∀ i ∈ B, (P.H * T + res).eval (embed (node i)) = embed (w i) := by
    refine ⟨A, hA, fun i hi => ?_⟩
    rw [← hST, extend, Polynomial.eval_map, Polynomial.eval₂_at_apply, hhits i hi]
  have hcontact := rawContact_of_restore 5000 w P.H res (P.z γ) (box.b + box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho := raw_locator_order w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact trueOrder_of_raw P.H res T (P.z γ) (box.b + box.j) (k + 1) F Q
    P.monic.ne_zero hrestore ho
private theorem source_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : Low6966Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (hh : P.H.natDegree ≤ 2316) {d : ℕ} (hd : t + d ≤ 5000 * 179759) :
    MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) d := by
  set z := inclConst (P.z γ)
  set y := trajectory (extend (s γ))
  apply mixedOrder_iff_coeff.mpr
  intro m hm
  let a : SeedVar →₀ ℕ := Finsupp.single none (m none)
  let b : SeedVar →₀ ℕ := m.some.optionElim 0
  have hab : a + b = m := by
    ext i
    cases i <;> simp [a, b]
  have hdis : ∀ i, i ∉ a.support ∨ i ∉ b.support := by
    intro i
    cases i <;> simp [a, b, Finsupp.mem_support_iff]
  have hlt : t + 6948 * m none + 48690 * m.some.degree < 5000 * 179759 := by
    change 6948 * m none + 48690 * m.some.degree < d at hm
    omega
  have hD := seed_motion w P L hh box t F hF (m none)
  have ho := fixed_seed_order h2 hw P L hD hγ m.some.degree hlt
  have hc := coeff_eq_zero_of_lowerOrder ho m.some (Nat.lt_succ_self _)
  change (K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F)))).coeff m.some = 0 at hc
  have hmap :
      K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F))) =
        MvPolynomial.C (inclX (P.H ^ (3 * m none))) *
          K1_13_4.translate y (atSeed z (toGeneric (mixedHasse a F))) := by
    simp [clearedSeed, toGeneric, a, atSeed, K1_13_4.translate]
  rw [hmap, MvPolynomial.coeff_C_mul] at hc
  have hn : inclX (P.H ^ (3 * m none)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericX)).mpr (pow_ne_zero _ P.monic.ne_zero)
  have hcoef := (mul_eq_zero.mp hc).resolve_left hn
  rw [translate_atSeed, coeff_atSeed_zero, ← partial_eq_mixedHasse, toGeneric, map_partial,
    translate_partial] at hcoef
  change (hasse a (K1_13_4.translate (atPoint z y) (toGeneric F))).coeff b = 0 at hcoef
  rw [coeff_partial_eq_of_disjoint _ _ _ hdis, hab] at hcoef
  exact hcoef
private theorem mixedHasse_order (F : PhysicalRow) (a : SeedVar →₀ ℕ)
    (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hF : MixedOrder (toGeneric F) z y (d + mixedWeight a)) :
    MixedOrder (toGeneric (mixedHasse a F)) z y d := by
  apply mixedOrder_iff_coeff.mpr
  intro b hb
  have hlt : mixedWeight (a + b) < d + mixedWeight a := by rw [mixedWeight_add]; omega
  have hz := mixedOrder_iff_coeff.mp hF _ hlt
  rw [← partial_eq_mixedHasse, toGeneric, map_partial, translate_partial]
  exact coeff_partial_eq_zero _ _ _ hz
theorem proof : Low6966Fat.c3 := by
  intro w Γ s hw P L hh
  let h2 := K1_13_4_3_2.proof
  constructor
  · intro F hF γ hγ
    exact source_order h2 hw P L hF.1 hγ hh (Nat.sub_add_cancel (show 4086972 ≤ 898795000 from by decide)).le
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h2 hw P L hF.1 hγ hh
      change t + mixedWeight a ≤ 5000 * 179759 - 1814603 at ht
      change t + (1814603 + mixedWeight a) ≤ 5000 * 179759
      omega
    | zero =>
      exact mixedOrder_iff_coeff.mpr (fun _ _ => by simp [toGeneric])
    | add Q R _ _ hQ hR =>
      exact mixedOrder_iff_coeff.mpr (fun a ha => by
        simp only [toGeneric, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
        exact (congrArg₂ (· + ·)
          (mixedOrder_iff_coeff.mp hQ a ha) (mixedOrder_iff_coeff.mp hR a ha)).trans (add_zero 0))
    | smul c Q _ hQ =>
      apply mixedOrder_iff_coeff.mpr
      intro a ha
      have hsmul : c • Q = MvPolynomial.C (Polynomial.C c) * Q := by
        rw [Algebra.smul_def]
        rfl
      rw [hsmul]
      simp only [toGeneric, map_mul, MvPolynomial.map_C, K1_13_4.translate, MvPolynomial.eval₂Hom_C,
        MvPolynomial.coeff_C_mul]
      exact mul_eq_zero.mpr (Or.inr (mixedOrder_iff_coeff.mp hQ a ha))
end
end Low6966FatContacts
end

#print axioms Low6966FatContacts.proof

end Merged6967_Fat6966Contacts

section Merged6967_Fat6966Padding
set_option Elab.async false


set_option Elab.async false

-- merged module R6960Low6966FatEliminate
section Merged_R6960Low6966FatEliminate

set_option Elab.async false
section
namespace Low6966Fat
noncomputable section
open K1 K1_13 K1_13_4_5
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
private theorem mixedWeight_pos {a : SeedVar →₀ ℕ} (ha : a ≠ 0) : 0 < mixedWeight a := by
  by_contra! h
  change 6948 * a none + 48690 * a.some.degree ≤ 0 at h
  have hn : a none = 0 := by omega
  have hd : a.some.degree = 0 := by omega
  have hs := (Finsupp.degree_eq_zero_iff _).mp hd
  apply ha
  ext i
  cases i with
  | none => simpa using hn
  | some i => simpa using DFunLike.congr_fun hs i
private theorem order_cancel_coeff (A B : GenericRow) (d : ℕ) (hA : A.coeff 0 ≠ 0)
    (hAB : ∀ a, mixedWeight a < d → (A * B).coeff a = 0) :
    ∀ a, mixedWeight a < d → B.coeff a = 0 := by
  classical
  suffices h : ∀ n a, mixedWeight a = n → n < d → B.coeff a = 0 by
    exact fun a ha => h _ a rfl ha
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a ha hd
    have hab := hAB a (ha.symm ▸ hd)
    rw [MvPolynomial.coeff_mul, Finset.sum_eq_single_of_mem (0, a) (by simp)] at hab
    · exact (mul_eq_zero.mp hab).resolve_left hA
    · intro b hb hbne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hb₁ : b.1 ≠ 0 := by
        intro hz
        apply hbne
        exact Prod.ext hz (by simpa [hz] using hs)
      have hw := mixedWeight_add b.1 b.2
      rw [hs, ha] at hw
      have hpos := mixedWeight_pos hb₁
      rw [ih (mixedWeight b.2) (by omega) b.2 rfl (by omega), mul_zero]
private theorem translated_const (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) :
    (translate (atPoint z y) F).coeff 0 = MvPolynomial.eval (atPoint z y) F := by
  let e : GenericRow →+* GenericX := MvPolynomial.eval (fun _ => 0)
  have he : e.comp (K1_13_4.translate (atPoint z y)) = MvPolynomial.eval (atPoint z y) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [e, K1_13_4.translate]
    · intro i
      simp [e, K1_13_4.translate]
  rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero']
  exact DFunLike.congr_fun he F
private theorem mixedOrder_cancel (A B : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hA : MvPolynomial.eval (atPoint z y) A ≠ 0) (h : MixedOrder (A * B) z y d) :
    MixedOrder B z y d := by
  intro a ha
  by_contra! hlt
  refine (MvPolynomial.mem_support_iff.mp ha) (order_cancel_coeff
    (translate (atPoint z y) A) (translate (atPoint z y) B) d ?_ ?_ a hlt)
  · rwa [translated_const]
  · intro b hb
    rw [← map_mul]
    by_contra hne
    exact (Nat.not_lt_of_ge (h b (MvPolynomial.mem_support_iff.mpr hne))) hb
open P3_6_4 (moving_lower total_prod index_prod eval_prod_factor_ne_zero)
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → (Polynomial Geom))
    (hzinj : Function.Injective z) {F G : GenericRow} (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, PairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
      ∃ (book : Finset K) (Q : Lower), book.card ≤ 56000 ∧ Q ≠ 0 ∧
        Q.totalDegree ≤ 1517 ∧ lowerIndex Q ≤ 492 ∧
        ∀ γ ∈ Γ, γ ∉ book → MvPolynomial.eval (trajectory (S γ)) Q = 0 ∨
          PairOrders D.left D.right (inclConst (z γ)) (trajectory (S γ)) := by
  classical
  have fix_ne (f : GenericRow) (hf : f ∈ D.fixed) : f ≠ 0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f : GenericRow) (hf : f ∈ D.moving) : f ≠ 0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total : (∑ f ∈ D.moving, jetTotal f) ≤ 17 := by
    simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f ∈ D.moving, jetIndex f) ≤ 5 := by
    simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 41 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 41 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_seed
  choose! q qn qt qi qe using
    (fun f hf => fixed_lower f (fix_ne f hf) (D.fixed_kind f hf).2.2)
  have exists_moving (f : GenericRow) (hf : f ∈ D.moving) :=
    moving_lower f (D.moving_kind f hf).1 (D.moving_kind f hf).2.1
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_total)
      (D.moving_kind f hf).2.2.1 (D.moving_kind f hf).2.2.2
  choose! r rn rt ri re using exists_moving
  let P : Lower := ∏ f ∈ D.fixed, q f
  let R : Lower := ∏ f ∈ D.moving, r f
  have Pn : P ≠ 0 := Finset.prod_ne_zero_iff.mpr qn
  have Rn : R ≠ 0 := Finset.prod_ne_zero_iff.mpr rn
  have Pt : P.totalDegree ≤ 123 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 123
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 41 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 41
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 41 * 17 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 41 * 17
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 41) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 5 + 1) * 41 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 5 + 1) * 41
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 41) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 41) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 56000 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 123 + 2 * 41 * 17 ≤ 1517 by decide)
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 41 + (2 * 5 + 1) * 41 ≤ 492 by decide)
  · intro γ hγ hnot
    let a := inclConst (z γ)
    let y := trajectory (S γ)
    change MvPolynomial.eval y (P * R) = 0 ∨ PairOrders D.left D.right a y
    by_cases hn : MvPolynomial.eval y (P * R) = 0
    · exact Or.inl hn
    rw [map_mul] at hn
    have hfixed (f : GenericRow) (hf : f ∈ D.fixed) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      rw [qe f hf]
      exact eval_prod_factor_ne_zero (left_ne_zero_of_mul hn) hf
    have hmoving (f : GenericRow) (hf : f ∈ D.moving) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      intro h0
      exact (eval_prod_factor_ne_zero (right_ne_zero_of_mul hn) hf) (re f hf _ _ h0)
    have hp : D.pure.eval a ≠ 0 := fun he => hnot (mem_seedBook.mpr ⟨hγ, he⟩)
    let A := pureSeed D.pure * (∏ f ∈ D.fixed, f ^ D.exponent f) *
      (∏ f ∈ D.moving, f ^ D.exponent f)
    have hA : MvPolynomial.eval (atPoint a y) A ≠ 0 := by
      simp only [A, map_mul, map_prod, map_pow, pure_eval]
      exact mul_ne_zero (mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hfixed f hf))) (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hmoving f hf))
    refine Or.inr ⟨mixedOrder_cancel A D.left a y _ hA ?_,
      mixedOrder_cancel A D.right a y _ hA ?_⟩
    · simpa only [A, ← D.left_eq] using (hOrders γ hγ).1
    · simpa only [A, ← D.right_eq] using (hOrders γ hγ).2
end
end Low6966Fat
end
section
namespace Low6966Fat
open Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open P3_6_4 (resultant_taylor_formal)
private def weight (d i : ℕ) : ℕ := d - 6948 * i
private def power (w : ℕ) : ℕ := (48689 + w) / 48690
private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : (Polynomial (Polynomial k))) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 6948 * i + 48690 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 48690 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstOrder j) (fun j : Fin n => weight secondOrder j)
private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : (Polynomial (Polynomial k))) (m n : ℕ)
    (hF : ∀ i l : ℕ, 6948 * i + 48690 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 6948 * i + 48690 * l < secondOrder → (G.coeff i).coeff l = 0)
    (i j : Fin (m + n)) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (firstOrder + secondOrder) i - columnWeight j) ∣
      sylvester F G m n i j := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, columnWeight, Set.mem_Icc]
    split_ifs with h
    · simpa only [add_comm secondOrder firstOrder] using
        coefficient_bound G secondOrder firstOrder i j h.1 hG
    · exact dvd_zero _
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right, columnWeight, Set.mem_Icc]
    split_ifs with h
    · exact coefficient_bound F firstOrder secondOrder i j h.1 hF
    · exact dvd_zero _
private theorem det_bound {k : Type*} [CommRing k] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial k)) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : (Polynomial k)) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 48690 * D ≤ (∑ i, row i) + 48689) :
    (Polynomial.X : (Polynomial k)) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : (Polynomial k)) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 48690 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _
private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 6948 * t)
    (hbefore : ∀ i < t, 6948 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 6948 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 6948 * (∑ i ∈ Finset.range t, i) =
      t * d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range t, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := hbefore i (Finset.mem_range.mp hi)
        unfold weight
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [Finset.sum_range_id] at hsum
  omega
private theorem benchmark_budget :
    (∑ j : Fin (24000 + 32000), columnWeight (m := 24000) (n := 32000) j) + 48690 * 21923 ≤
      (∑ i : Fin (24000 + 32000), weight (firstOrder + secondOrder) i) + 48689 := by
  have hF : (∑ i : Fin 24000, weight firstOrder i) = 1204069140 := by
    rw [sum_weight (t := 589) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder]; omega)]
    decide
  have hG : (∑ i : Fin 32000, weight secondOrder i) = 237866918 := by
    rw [sum_weight (t := 262) (by decide) (by decide)
      (by intro i hi; simp only [secondOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (24000 + 32000), weight (firstOrder + secondOrder) i) =
      2509326650 := by
    rw [sum_weight (t := 850) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder, secondOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide
private theorem resultant_bound
    (F G : (Polynomial (Polynomial GenericX))) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 6948 * i + 48690 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 6948 * i + 48690 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 48690 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 48689) :
    (Polynomial.X : (Polynomial GenericX)) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget
theorem line_resultant_order (F G : (Polynomial (Polynomial GenericX))) (z : GenericX)
    (hF : F.natDegree ≤ 24000) (hG : G.natDegree ≤ 32000)
    (hFO : ∀ i j, 6948 * i + 48690 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 6948 * i + 48690 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : (Polynomial GenericX)) ^ 21923 ∣ Polynomial.resultant F G 24000 32000 := by
  exact resultant_bound F G z (m := 24000) (n := 32000) (D := 21923)
    hF hG hFO hGO benchmark_budget
end Low6966Fat
end
section
namespace Low6966Fat
noncomputable section
open K1_13 Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped BigOperators
set_option maxRecDepth 4000
private def ray (v : Fin 3 → GenericX) : Lower →+* (Polynomial GenericX) :=
  MvPolynomial.eval₂Hom C (fun i => C (v i) * Polynomial.X)
private theorem ray_monomial (v : Fin 3 → GenericX) (a : Fin 3 →₀ ℕ) (c : GenericX) :
    ray v (MvPolynomial.monomial a c) =
      monomial a.degree (MvPolynomial.eval v (MvPolynomial.monomial a c)) := by
  rw [← C_mul_X_pow_eq_monomial]
  simp only [ray, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial, mul_pow,
    Finsupp.prod]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, ← mul_assoc]
  simp only [map_mul, map_prod, map_pow]
private theorem ray_coeff (v : Fin 3 → GenericX) (Q : Lower) (j : ℕ) :
    (ray v Q).coeff j = MvPolynomial.eval v (MvPolynomial.homogeneousComponent j Q) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [ray_monomial, coeff_monomial,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases h : a.degree = j
    · simp [h]
    · simp [h, Ne.symm h]
  | add Q R hQ hR =>
    rw [map_add, coeff_add, hQ, hR, map_add, map_add]
private theorem line_translation (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX) :
    ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp (Polynomial.X + C (C z)) =
      (asSeedPoly (K1_13_4.translate (atPoint z y) F)).map (ray v) := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let left := (compRingHom (Polynomial.X + C (C z))).comp ((mapRingHom ((ray v).comp (K1_13_4.translate y))).comp e)
  let right := (mapRingHom (ray v)).comp (e.comp (K1_13_4.translate (atPoint z y)))
  have he : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, e, K1_13_4.translate, ray]
    · intro i
      cases i <;>
        simp [left, right, e, K1_13_4.translate, ray, atPoint]
  exact DFunLike.congr_fun he F
private theorem line_order (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX)
    (d : ℕ) (hF : MixedOrder F z y d) :
    ∀ i j, 6948 * i + 48690 * j < d →
      ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).taylor (C z)).coeff i).coeff j = 0 := by
  intro i j h
  change ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp
    (Polynomial.X + C (C z))).coeff i).coeff j = 0
  rw [line_translation, coeff_map, ray_coeff]
  suffices hc : MvPolynomial.homogeneousComponent j
      ((asSeedPoly (K1_13_4.translate (atPoint z y) F)).coeff i) = 0 by
    rw [hc, map_zero]
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro a ha hj
  have hmem : a.optionElim i ∈ (K1_13_4.translate (atPoint z y) F).support := by
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    exact ha
  have hb := hF _ hmem
  have hweight : mixedWeight (a.optionElim i) = 6948 * i + 48690 * j := by
    change 6948 * a.optionElim i none + 48690 * (a.optionElim i).some.degree = _
    rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim, hj]
  rw [hweight] at hb
  exact (Nat.not_lt_of_ge hb) h
private theorem order_of_rays (Q : Lower) (y : Fin 3 → GenericX) (d : ℕ)
    (h : ∀ v, Polynomial.X ^ d ∣ ray v (K1_13_4.translate y Q)) :
    LowerOrder Q y d := by
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  intro a ha
  change d ≤ a.degree
  by_contra! ha'
  have hm : MvPolynomial.homogeneousComponent a.degree (K1_13_4.translate y Q) = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, ← ray_coeff]
    exact (X_pow_dvd_iff (n := d) (f := ray v (K1_13_4.translate y Q))).mp (h v) a.degree ha'
  have hc := congrArg (fun P : Lower => P.coeff a) hm
  simp [MvPolynomial.coeff_homogeneousComponent] at hc
  exact (MvPolynomial.mem_support_iff.mp ha) hc
def seedResultant27 (F G : GenericRow) : Lower :=
  Polynomial.resultant (asSeedPoly F) (asSeedPoly G) 24000 32000
private theorem line_resultant (F G : GenericRow) (y v : Fin 3 → GenericX) :
    resultant ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y)))
      ((asSeedPoly G).map ((ray v).comp (K1_13_4.translate y))) 24000 32000 =
        ray v (K1_13_4.translate y (seedResultant27 F G)) := by
  unfold seedResultant27
  rw [resultant_map_map, RingHom.comp_apply]
theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : (Polynomial Geom)) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)
theorem resultant_order (F G : GenericRow) (z : GenericX)
    (y : Fin 3 → GenericX) (hF : (asSeedPoly F).natDegree ≤ 24000)
    (hG : (asSeedPoly G).natDegree ≤ 32000) (h : PairOrders F G z y) :
    LowerOrder (seedResultant27 F G) y 21923 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact line_resultant_order _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)
end
end Low6966Fat
end

#print axioms Low6966Fat.resultant_order

end Merged_R6960Low6966FatEliminate

-- merged module Fat6966Padding
section Merged_Fat6966Padding

set_option Elab.async false
/-! Low-specific padding of a coprime pair to seed degree exactly 27,0 and the resulting
resultant box (367,443,0, 124,200,0); a copy of the padding part of `Fast074`. -/
section
namespace Low6966Fat
noncomputable section
open K1_13 K1_13_4 Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open K1_13_4_6 (Fiber toFiber embedConstant toFiber_injective coprime_in_fiber exists_constant_nonroot coprime_linear asSeedPoly_ne_zero deg deg_pad_coeff deg_resultant)
structure PaddedPair27 (F G : GenericRow) where
  a : (Polynomial Geom)
  b : (Polynomial Geom)
  degree_left : (asSeedPoly (pad F a)).natDegree = 24000
  degree_right : (asSeedPoly (pad G b)).natDegree = 32000
  nonzero : seedResultant27 (pad F a) (pad G b) ≠ 0
  total : (seedResultant27 (pad F a) (pad G b)).totalDegree ≤ 380928000
  index : lowerIndex (seedResultant27 (pad F a) (pad G b)) ≤ 128800000
  keeps_order : ∀ z y, PairOrders F G z y → PairOrders (pad F a) (pad G b) z y
private theorem pad_degree27 {cap : ℕ} (F : GenericRow) (hF : F ≠ 0)
    (hcap : seedDegree F ≤ cap) (a : Geom) :
    (asSeedPoly (pad F (((Polynomial.X : (Polynomial Geom)) - C a) ^
      (cap - (asSeedPoly F).natDegree)))).natDegree = cap := by
  have hcap' : (asSeedPoly F).natDegree ≤ cap := by
    simpa only [asSeedPoly, MvPolynomial.natDegree_optionEquivLeft, seedDegree] using hcap
  rw [K1_13_4_6.asSeedPoly_pad, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    natDegree_mul (asSeedPoly_ne_zero hF) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_X_sub_C, mul_one, Nat.add_sub_of_le hcap']
theorem padding_exists27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0)
    (hfg : IsRelPrime F G) (hf : seedDegree F ≤ 24000) (hg : seedDegree G ≤ 32000) :
    ∃ a b : (Polynomial Geom), (asSeedPoly (pad F a)).natDegree = 24000 ∧
      (asSeedPoly (pad G b)).natDegree = 32000 ∧ seedResultant27 (pad F a) (pad G b) ≠ 0 := by
  classical
  let f := (asSeedPoly F).map toFiber
  let g := (asSeedPoly G).map toFiber
  have hf0 : f ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hF)
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hG)
  have hcop : IsCoprime f g := by
    apply coprime_in_fiber (asSeedPoly_ne_zero hF)
    intro d hdf hdg
    let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
    have hu : IsUnit (e.symm d) :=
      hfg (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdf)
        (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdg)
    have he := hu.map e.toRingHom
    change IsUnit (e (e.symm d)) at he
    rwa [e.apply_symm_apply] at he
  obtain ⟨a, ha, _⟩ := exists_constant_nonroot g hg0 ∅
  obtain ⟨b, hb, hba⟩ := exists_constant_nonroot f hf0 {toFiber (embedConstant a)}
  let p := ((Polynomial.X : (Polynomial Geom)) - C a) ^ (24000 - (asSeedPoly F).natDegree)
  let q := ((Polynomial.X : (Polynomial Geom)) - C b) ^ (32000 - (asSeedPoly G).natDegree)
  have hp : (asSeedPoly (pad F p)).natDegree = 24000 := pad_degree27 F hF hf a
  have hq : (asSeedPoly (pad G q)).natDegree = 32000 := pad_degree27 G hG hg b
  refine ⟨p, q, hp, hq, ?_⟩
  have hab : toFiber (embedConstant a) ≠ toFiber (embedConstant b) := by
    simpa using (Finset.notMem_singleton.mp hba).symm
  have hpad : IsCoprime ((asSeedPoly (pad F p)).map toFiber)
      ((asSeedPoly (pad G q)).map toFiber) := by
    simp only [K1_13_4_6.asSeedPoly_pad, Polynomial.map_mul, p, q, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact (hcop.mul_right (coprime_linear f hb).symm.pow_right).mul_left
      ((coprime_linear g ha).pow_left.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow)
  have hn := resultant_ne_zero _ _ hpad
  rw [natDegree_map_eq_of_injective toFiber_injective,
    natDegree_map_eq_of_injective toFiber_injective, hp, hq, resultant_map_map] at hn
  intro hz
  exact hn ((congrArg toFiber hz).trans (map_zero _))

theorem padded27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0) (hp : IsRelPrime F G)
    (hf : Low6966Fat.Caps27 firstBox F) (hg : Low6966Fat.Caps27 secondBox G) :
    Nonempty (PaddedPair27 F G) := by
  obtain ⟨a, b, ha, hb, hn⟩ := padding_exists27 hF hG hp (hf.2.trans (by decide)) (hg.2.trans (by decide))
  refine ⟨⟨a, b, ha, hb, hn, ?_, ?_, ?_⟩⟩
  · have h := deg_resultant (1 : Fin 3 → ℕ) (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      24000 32000 6789 6820 (fun i => (deg_pad_coeff _ F a i).trans hf.1.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.1)
    simpa only [MvPolynomial.weightedTotalDegree_one, seedResultant27,
      ← Nat.mul_add, Nat.add_comm 6820 6789] using h.trans_eq (by norm_num)
  · have h := deg_resultant Fin.val (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      24000 32000 2300 2300 (fun i => (deg_pad_coeff _ F a i).trans hf.1.2.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.2.1)
    simpa only [MvPolynomial.weightedTotalDegree, Finsupp.weight_apply, Nat.nsmul_eq_mul,
      Nat.mul_comm, lowerIndex, seedResultant27, ← Nat.mul_add] using h.trans_eq (by norm_num)
  · intro z y h
    exact ⟨mixedOrder_pad a h.1, mixedOrder_pad b h.2⟩
end
end Low6966Fat
end

end Merged_Fat6966Padding

end Merged6967_Fat6966Padding

section Merged6967_GoldBranch7N4
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (HighBand agreement)
open P3_7 (Bank  debit jointGain   )
export P1_7_6 (orderEnd linearEnd Quad prefixProduct intervalProduct seedEnd yStart seedQuad scaledDebit)
def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m * agreement : ℕ) + (j : ℤ) - (131071 - (h : ℤ)) * q - 2 * (h : ℤ) * t
def surplus (h : ℕ) (b : Bank) (E v : ℕ) : ℤ :=
  (jointGain h b.shape E v : ℤ) - (debit h b : ℤ)
def colEnd (s : Shape) (h t : ℕ) : ℕ :=
  linearEnd (2*h*t) (131071-h) (s.m*agreement) (s.B+1)
def edgeShift (s : Shape) (h t : ℕ) : ℕ :=
  2*h*t + (131071-h)*colEnd s h t + 1 - s.m*agreement
def innerEnd (s : Shape) (h E v d t R : ℕ) : ℕ :=
  linearEnd (yStart E d t) (E-1) (colEnd s h t) (seedEnd s v d R)
def outerEnd (s : Shape) (h E v d t R : ℕ) : ℕ :=
  min (t+1-edgeShift s h t)
    (linearEnd (yStart E d t) (E-1) (colEnd s h t+1) (seedEnd s v d R))
def widthOrigin (s : Shape) (h t : ℕ) : ℤ :=
  (s.m*agreement : ℕ) + (t : ℤ) - 2*(h : ℤ)*t
def innerQuad (s : Shape) (h E d t : ℕ) : Quad :=
  let D : ℤ := (131071-h : ℕ)
  let k : ℤ := colEnd s h t
  let l : ℤ := yStart E d t
  let p : ℤ := (E-1 : ℕ)
  P1_7_6.Quad.ofLines (k-l) (-p) (2*widthOrigin s h t-D*(l+k-1)) (-2-D*p)
def outerQuad (s : Shape) (h t : ℕ) : Quad :=
  ⟨2*(widthOrigin s h t-((131071-h : ℕ) : ℤ)*colEnd s h t), -2, 0⟩
def phaseBlock (s : Shape) (h E v d t : ℕ) : ℤ :=
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let c := seedQuad s v d
  intervalProduct c (innerQuad s h E d t) L (innerEnd s h E v d t R) +
    if colEnd s h t < s.B+1 then
      intervalProduct c (outerQuad s h t) L (outerEnd s h E v d t R)
    else 0
def blockSurplus (s : Shape) (N P h E v : ℕ) : ℤ :=
  (∑ t ∈ range (s.J+orderEnd s E v), (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) -
    scaledDebit s N P h
def BlockChecks (s : Shape) (N P h E v : ℕ) : Prop :=
  0 < blockSurplus s N P h E v ∧ blockSurplus s N P h E v ≤ blockSurplus s N P (h+1) E v
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape shapeSum slots)
open P3 (agreement)
open P3_7 (Bank debit jointGain)
open P1_7_6 (rise_of_convex)
theorem width_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    (↑(s.m * agreement + j - q * (131071-h) - 2*h*t : ℕ) : ℤ) =
      max 0 (width s h q j t) := by
  rw [Nat.sub_sub]
  have hd : (↑(131071-h : ℕ) : ℤ) = 131071 - h := Nat.cast_sub hh
  have he : (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*t : ℕ) : ℤ) =
      width s h q j t := by
    simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hd]
    ring
  generalize s.m*agreement+j = x at *
  generalize q*(131071-h)+2*h*t = y at *
  by_cases hxy : y ≤ x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]
private theorem width_convex (s : Shape) (h q j t : ℕ) :
    max 0 (width s (h+1) q j t) + max 0 (width s (h+1) q j t) ≤
      max 0 (width s h q j t) + max 0 (width s (h+2) q j t) := by
  have hlin : width s (h+1) q j t + width s (h+1) q j t =
      width s h q j t + width s (h+2) q j t := by
    simp only [width, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases hn : width s (h+1) q j t ≤ 0
  · rw [max_eq_left hn, zero_add]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hn), hlin]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
private theorem weighted_convex (s : Shape) (h q j t c : ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (↑(c * (s.m * agreement + j - q*(131071-h) - 2*h*t) : ℕ) : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  dsimp only
  simp only [Nat.cast_mul, width_cast s h q j t (by omega),
    width_cast s (h+1) q j t (by omega), width_cast s (h+2) q j t hh, ← mul_add]
  exact mul_le_mul_of_nonneg_left (width_convex s h q j t) (Int.natCast_nonneg c)
private theorem gain_convex (s : Shape) (h E v : ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (jointGain h s E v : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  simp only [jointGain, shapeSum, Nat.cast_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  let g := (q-j)/E
  let raw := fun k a => s.m*agreement+j-q*(131071-k)-2*k*(j+a)
  let A := fun k => (↑(∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v))*raw k a : ℕ) : ℤ)
  let B := fun k => (↑(slots s.U (g*v)*raw k g : ℕ) : ℤ)
  simp only [Nat.cast_add]
  change A (h+1) + B (h+1) + (A (h+1) + B (h+1)) ≤ A h + B h + (A (h+2) + B (h+2))
  rw [add_add_add_comm (A (h+1)), add_add_add_comm (A h)]
  apply add_le_add
  · simp only [A, Nat.cast_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro a _
    exact weighted_convex s h q j (j+a) (slots s.U (a*v) - slots s.U ((a+1)*v)) hh
  · exact weighted_convex s h q j (j+(q-j)/E) (slots s.U (((q-j)/E)*v)) hh
private theorem debit_affine (h : ℕ) (b : Bank) :
    (debit (h+1) b : ℤ) + (debit (h+1) b : ℤ) =
      (debit h b : ℤ) + (debit (h+2) b : ℤ) := by
  simp only [debit, P1_7.debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring
private theorem surplus_convex (h : ℕ) (b : Bank) (E v : ℕ) (hh : h+2 ≤ 131071) :
    surplus (h+1) b E v + surplus (h+1) b E v ≤
      surplus h b E v + surplus (h+2) b E v := by
  have hg := gain_convex b.shape h E v hh
  have hd := debit_affine h b
  dsimp only at hg
  unfold surplus
  omega
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P3 (agreement)
open P3_7 (jointGain)
open P1_7_6 (slots_anti sum_range_guard diagonal)
def phase (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ t ∈ range (s.J + orderEnd s E v), ∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
    (slots s.U ((a+d)*v) : ℤ) *
      ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)
private theorem position_phases (s : Shape) (h E v q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => slots s.U (a*v)
    let x := s.m*agreement+j-q*(131071-h)
    let g := (q-j)/E
    let f := fun d a => (c (a+d) : ℤ)*max 0 (width s h q j (j+a))
    (↑((∑ a ∈ range g, (c a - c (a+1))*(x-2*h*(j+a))) + c g*(x-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+0) ≤ q then f 0 a else 0) -
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+1) ≤ q then f 1 a else 0) := by
  dsimp only
  let g := (q-j)/E
  let f := fun d a => (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a))
  have step (a : ℕ) : slots s.U ((a+1)*v) ≤ slots s.U (a*v) :=
    slots_anti _ (Nat.mul_le_mul_right v (by omega))
  have hdiff :
      (↑((∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
          (s.m*agreement+j-q*(131071-h)-2*h*(j+a))) +
        slots s.U (g*v)*(s.m*agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (g+1), f 0 a) - ∑ a ∈ range g, f 1 a := by
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sum]
    rw [show (∑ a ∈ range g, f 0 a) + f 0 g - (∑ a ∈ range g, f 1 a) =
        ((∑ a ∈ range g, f 0 a) - (∑ a ∈ range g, f 1 a)) + f 0 g by ring,
      ← sum_sub_distrib]
    simp only [Nat.cast_mul, width_cast s h _ _ _ hh, f, Nat.add_zero]
    have hs (a : ℕ) :
        (↑(slots s.U (a*v) - slots s.U ((a+1)*v) : ℕ) : ℤ) =
          (slots s.U (a*v) : ℤ) - slots s.U ((a+1)*v) := Int.ofNat_sub (step a)
    simp only [hs, sub_mul]
  rw [hdiff]
  have hz (d a : ℕ) (ha : orderEnd s E v ≤ a) (hg : a+d ≤ g) : f d a = 0 := by
    have hcap : g ≤ s.B/E := Nat.div_le_div_right (by omega)
    have hab : a < s.B/E+1 := by omega
    unfold orderEnd at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge : s.U/v < a+d := by omega
      have hout : s.U < (a+d)*v := by
        by_contra! hm
        exact (Nat.not_le_of_lt hlarge) ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)).2 hm)
      simp [f, slots, Nat.not_le_of_lt hout]
  have hdiv (a d : ℕ) : j+E*(a+d) ≤ q ↔ a+d ≤ g := by
    rw [Nat.le_div_iff_mul_le he, Nat.mul_comm (a+d) E]
    omega
  rw [sum_range_guard (g+1) _ (fun a ha hb => hz 0 a ha (by omega)),
    sum_range_guard g _ (fun a ha hb => hz 1 a ha (by omega))]
  have hzero (a : ℕ) : j+E*a ≤ q ↔ a ≤ g := by simpa using hdiv a 0
  simp only [hzero, Nat.add_zero, Nat.lt_succ_iff, Nat.add_one_le_iff, f]
private def phaseQ (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
    if j + E*(a+d) ≤ q then
      (slots s.U ((a+d)*v) : ℤ) * max 0 (width s h q j (j+a)) else 0
private theorem phaseQ_expand (s : Shape) (h E v d q : ℕ) :
    (∑ j ∈ range (min q s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0) =
    ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0 := by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
private theorem phaseQ_eq (s : Shape) (h E v d : ℕ) : phaseQ s h E v d = phase s h E v d := by
  have hR : orderEnd s E v-1+1 = orderEnd s E v := by
    apply Nat.sub_add_cancel
    unfold orderEnd
    split
    · exact Nat.succ_pos _
    · exact le_min (Nat.succ_pos _) (Nat.succ_pos _)
  unfold phaseQ phase
  rw [sum_comm]
  conv_lhs =>
    enter [2, j]
    rw [sum_comm]
  conv_lhs =>
    rw [← hR]
    rw [diagonal]
  rw [Nat.add_assoc, hR]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro a ha
  have hta : t-a+a = t := Nat.sub_add_cancel (by have := (mem_Ico.mp ha).2; omega)
  rw [mul_sum, ← sum_filter]
  have hf : (range (s.B+1)).filter (fun q => t-a+E*(a+d) ≤ q) =
      Ico (t-a+E*(a+d)) (s.B+1) := by
    ext q
    simp only [mem_range, mem_filter, mem_Ico]
    tauto
  rw [hf, hta]
end P3_7_4
end
section
namespace P3_7_4
open Finset
open P3 (agreement)
open K1_14 (Shape)
open K1_14_2_1 (twice_sum_linear)
export P1_7_6 (lt_linearEnd)
private theorem width_eq_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    width s h q j t = (↑(s.m*agreement+j : ℕ) : ℤ) -
      (↑(2*h*t+(131071-h)*q : ℕ) : ℤ) := by
  simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hh, Nat.cast_ofNat]
  ring
theorem width_sum (s : Shape) (h t j l : ℕ) (hh : h ≤ 131071) (hj : j ≤ 131071-h) :
    (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
      (∑ q ∈ Ico l (colEnd s h t), width s h q j t) +
        if colEnd s h t < s.B+1 ∧ l ≤ colEnd s h t ∧ edgeShift s h t ≤ j then
          width s h (colEnd s h t) j t else 0 := by
  let k := colEnd s h t
  let D := 131071-h
  have hk (q : ℕ) : q < k ↔ q < s.B+1 ∧ 2*h*t + D*q < s.m*agreement :=
    lt_linearEnd _ _ _ _ _
  have hkB : k ≤ s.B+1 := by
    by_contra! h
    exact (Nat.lt_irrefl _) ((hk (s.B+1)).mp h).1
  have hpos (q : ℕ) (hq : q < k) : 0 ≤ width s h q j t := by
    have hp := ((hk q).mp hq).2
    rw [width_eq_cast s h q j t hh]
    change 2*h*t+D*q < s.m*agreement at hp
    change 0 ≤ (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*q : ℕ) : ℤ)
    omega
  have hsum : (∑ q ∈ Ico l k, max 0 (width s h q j t)) = ∑ q ∈ Ico l k, width s h q j t := by
    apply sum_congr rfl
    intro q hq
    exact max_eq_right (hpos q (mem_Ico.mp hq).2)
  by_cases hb : k < s.B+1
  · have hbase : s.m*agreement ≤ 2*h*t + D*k := by
      by_contra! he
      exact (Nat.lt_irrefl _) ((hk k).mpr ⟨hb,he⟩)
    have hzero (q : ℕ) (hq : k < q) : max 0 (width s h q j t) = 0 := by
      have hm : D*(k+1) ≤ D*q := Nat.mul_le_mul_left D (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      apply max_eq_left
      rw [width_eq_cast s h q j t hh]
      change j ≤ D at hj
      change (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*q : ℕ) : ℤ) ≤ 0
      omega
    have hrestrict :
        (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
          ∑ q ∈ Ico l (k+1), max 0 (width s h q j t) := by
      symm
      apply sum_subset
      · intro q hq
        obtain ⟨ha,he⟩ := mem_Ico.mp hq
        exact mem_Ico.mpr ⟨ha,by omega⟩
      · intro q hq hn
        obtain ⟨ha,he⟩ := mem_Ico.mp hq
        exact hzero q (by
          by_contra! hle
          exact hn (mem_Ico.mpr ⟨ha,by omega⟩))
    change _ = (∑ q ∈ Ico l k, _) + if k < s.B+1 ∧ l ≤ k ∧ edgeShift s h t ≤ j then _ else _
    rw [hrestrict]
    by_cases hl : l ≤ k
    · rw [sum_Ico_succ_top hl, hsum]
      simp only [hb, hl, true_and]
      congr 1
      have hsign : 0 < width s h k j t ↔ edgeShift s h t ≤ j := by
        rw [width_eq_cast s h k j t hh]
        change (0 : ℤ) < (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*k : ℕ) : ℤ) ↔
          2*h*t+D*k+1-s.m*agreement ≤ j
        omega
      by_cases hw : edgeShift s h t ≤ j
      · rw [ite_eq_left hw, max_eq_right ((hsign.mpr hw).le)]
      · rw [ite_eq_right hw, max_eq_left (by have := mt hsign.mp hw; omega)]
    · have he : Ico l (k+1) = ∅ := Ico_eq_empty_of_le (by omega)
      have hf : Ico l k = ∅ := Ico_eq_empty_of_le (by omega)
      simp [he,hf,hl]
  · have he : k = s.B+1 := by omega
    change _ = (∑ q ∈ Ico l k, _) + if k < s.B+1 ∧ l ≤ k ∧ edgeShift s h t ≤ j then _ else _
    rw [← he, hsum]
    simp
theorem twice_width_interval (s : Shape) (h t j l k : ℕ) (hh : h ≤ 131071)
    (hl : l ≤ k) :
    2 * (∑ q ∈ Ico l k, width s h q j t) =
      ((k : ℤ)-l) * (2*((s.m*agreement : ℕ)+(j : ℤ)-2*(h : ℤ)*t) -
        ((131071-h : ℕ) : ℤ)*((l : ℤ)+k-1)) := by
  rw [sum_Ico_eq_sum_range]
  have hf (a : ℕ) : width s h (l+a) j t =
      width s h l j t + (-((131071-h : ℕ) : ℤ))*(a : ℤ) := by
    simp only [width, Nat.cast_add, Nat.cast_sub hh, Nat.cast_ofNat]
    ring
  simp_rw [hf]
  rw [twice_sum_linear]
  simp only [Nat.cast_sub hl, width, Nat.cast_sub hh, Nat.cast_ofNat]
  ring
end P3_7_4
end
section
namespace P3_7_4
open Finset
open P3 (agreement)
open K1_14 (Shape slots triangle)
open P3_7 (debit)
open P1_7_6 (intervalProduct_eq)
open P1_7_6 (lt_seedEnd yStart_eq seedQuad_eq sum_clipped)
private theorem widthOrigin_eq (s : Shape) (h t a q : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    width s h q (t-a) t = widthOrigin s h t - a - ((131071-h : ℕ) : ℤ)*q := by
  simp only [width, widthOrigin, Nat.cast_sub hh, Nat.cast_sub ha, Nat.cast_ofNat]
  ring
private theorem innerQuad_eq (s : Shape) (h E d t a : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (ha : a ≤ t) (hl : t-a+E*(a+d) ≤ colEnd s h t) :
    2*(∑ q ∈ Ico (t-a+E*(a+d)) (colEnd s h t), width s h q (t-a) t) =
      (innerQuad s h E d t).eval a := by
  rw [twice_width_interval s h t (t-a) _ _ hh hl, innerQuad, P1_7_6.Quad.eval_ofLines,
    yStart_eq E d t a he ha]
  simp only [widthOrigin, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  ring
private theorem outerQuad_eq (s : Shape) (h t a : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    2*width s h (colEnd s h t) (t-a) t = (outerQuad s h t).eval a := by
  rw [widthOrigin_eq s h t a _ hh ha]
  simp only [outerQuad, P1_7_6.Quad.eval]
  ring
theorem phaseBlock_eq (s : Shape) (h E v d t : ℕ)
    (hh : h ≤ 131071) (hj : s.J ≤ 131071-h) (he : 0 < E) :
    240*(∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
      (slots s.U ((a+d)*v) : ℤ) *
        ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)) =
      phaseBlock s h E v d t := by
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let k := colEnd s h t
  let l := fun a => t-a+E*(a+d)
  let c := fun a => (slots s.U ((a+d)*v) : ℤ)
  let inner := fun a => ∑ q ∈ Ico (l a) k, width s h q (t-a) t
  let outer := fun a =>
    if k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a then width s h k (t-a) t else 0
  let R₁ := innerEnd s h E v d t R
  let R₂ := outerEnd s h E v d t R
  have ht (a : ℕ) (ha : a < R) : a ≤ t :=
    (Nat.le_of_lt_succ ha).trans (min_le_left _ _)
  have hcore (a : ℕ) : a < R₁ ↔ a < R ∧ (a+d)*v ≤ s.U ∧ l a < k := by
    simp only [R₁, innerEnd, lt_linearEnd, lt_seedEnd]
    constructor
    · rintro ⟨⟨ha,hv⟩,hk⟩
      exact ⟨ha,hv,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
    · rintro ⟨ha,hv,hk⟩
      exact ⟨⟨ha,hv⟩,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
  have hedge (a : ℕ) :
      a < R₂ ↔ a < R ∧ (a+d)*v ≤ s.U ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a := by
    simp only [R₂, outerEnd, lt_min_iff, lt_linearEnd, lt_seedEnd]
    constructor
    · rintro ⟨hs,⟨ha,hv⟩,hk⟩
      refine ⟨ha,hv,?_,by omega⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
    · rintro ⟨ha,hv,hk,hs⟩
      refine ⟨by have := ht a ha; omega,⟨ha,hv⟩,?_⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
  have hw (a : ℕ) (ha : a ∈ Ico L R) :
      (∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) = inner a + outer a := by
    obtain ⟨ha₀,_⟩ := mem_Ico.mp ha
    exact width_sum s h t (t-a) (l a) hh ((by dsimp [L] at ha₀; omega : t-a ≤ s.J).trans hj)
  have hsplit :
      (∑ a ∈ Ico L R, c a * ∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) =
        (∑ a ∈ Ico L R, c a * inner a) + (∑ a ∈ Ico L R, c a * outer a) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a ha => by rw [hw a ha, mul_add])
  have normalize (x y : ℤ) : 4*(x*y) = (2*x)*(2*y) := by ring
  have hi :
      4*(∑ a ∈ Ico L R, c a * inner a) =
        ∑ a ∈ Ico L R₁, (seedQuad s v d).eval a * (innerQuad s h E d t).eval a := by
    rw [mul_sum]
    apply sum_clipped (fun a ha => ((hcore a).mp ha).1)
    · intro a ha hn
      have haR := (mem_Ico.mp ha).2
      by_cases hv : (a+d)*v ≤ s.U
      · have hl : k ≤ l a := by
          by_contra! hl
          exact (Nat.not_lt_of_ge hn) ((hcore a).mpr ⟨haR,hv,hl⟩)
        simp [inner, Ico_eq_empty_of_le hl]
      · simp [c, slots, hv]
    · intro a ha
      obtain ⟨haR,hv,hl⟩ := (hcore a).mp (mem_Ico.mp ha).2
      rw [normalize, seedQuad_eq s v d a hv, ← innerQuad_eq s h E d t a hh he (ht a haR) hl.le]
  have ho :
      240*(∑ a ∈ Ico L R, c a * outer a) =
        if k < s.B+1 then intervalProduct (seedQuad s v d) (outerQuad s h t) L R₂ else 0 := by
    by_cases hk : k < s.B+1
    · rw [ite_eq_left hk, ← intervalProduct_eq, show (240 : ℤ) = 60*4 by decide, mul_assoc, mul_sum]
      congr 1
      apply sum_clipped (fun a ha => ((hedge a).mp ha).1)
      · intro a ha hn
        have haR := (mem_Ico.mp ha).2
        by_cases hv : (a+d)*v ≤ s.U
        · have hbound : ¬(k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a) :=
            fun ⟨_,hl,hs⟩ => (Nat.not_lt_of_ge hn) ((hedge a).mpr ⟨haR,hv,hl,hs⟩)
          simp only [outer, ite_eq_right hbound, mul_zero]
        · simp [c, slots, hv]
      · intro a ha
        obtain ⟨haR,hv,hl,hs⟩ := (hedge a).mp (mem_Ico.mp ha).2
        rw [normalize, seedQuad_eq s v d a hv, ← outerQuad_eq s h t a hh (ht a haR)]
        simp only [outer, hk, hl, hs, and_self, ite_true]
        rfl
    · simp [outer, hk]
  change _ = intervalProduct _ _ L R₁ + if k < s.B+1 then intervalProduct _ _ L R₂ else 0
  rw [hsplit, mul_add, ho, ← intervalProduct_eq (seedQuad s v d) (innerQuad s h E d t), ← hi]
  ring
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (agreement)
open P1_7_6 (intervalProduct_eq)
open P1_7_6_4 (Core corePrefix diagonalCore)
open P1_7_6 (lt_seedEnd)
def bankCore (s : Shape) (h E v d k : ℕ) : Core :=
  let D : ℤ := (131071-h : ℕ)
  let p : ℤ := (E-1 : ℕ)
  let w : ℤ := (E*d : ℕ)
  ⟨k,E*d,E-1,seedEnd s v d (orderEnd s E v),seedQuad s v d,
    ⟨(k : ℤ)-w,-p⟩, ⟨2*(s.m*agreement : ℕ)-D*(w+k-1),-2-D*p⟩,
    2-4*(h : ℤ)-D⟩
def outerPart (s : Shape) (h E v d t : ℕ) : ℤ :=
  if colEnd s h t < s.B+1 then
    intervalProduct (seedQuad s v d) (outerQuad s h t) (t-s.J)
      (outerEnd s h E v d t (min t (orderEnd s E v-1)+1))
  else 0
private theorem diagonal_eq (s : Shape) (h E v d t k : ℕ) (hk : colEnd s h t = k) :
    phaseBlock s h E v d t = 60*diagonalCore (bankCore s h E v d k) s.J t + outerPart s h E v d t := by
  let C := bankCore s h E v d k
  let R := min t (orderEnd s E v-1)+1
  change intervalProduct (seedQuad s v d) (innerQuad s h E d t) (t-s.J)
      (innerEnd s h E v d t R) + outerPart s h E v d t =
    60*diagonalCore C s.J t + outerPart s h E v d t
  rw [← intervalProduct_eq, diagonalCore, ← sum_filter]
  congr 2
  have hmem : Ico (t-s.J) (innerEnd s h E v d t R) =
      (range C.cap).filter (fun a => a ≤ t ∧ t < a+(s.J+1) ∧ t+(C.offset+C.step*a) < C.column) := by
    have hend : 0 < orderEnd s E v := by
      unfold orderEnd
      split
      · exact Nat.succ_pos _
      · exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)
    ext a
    simp only [mem_Ico, mem_filter, mem_range, C, bankCore, innerEnd, lt_linearEnd, lt_seedEnd,
      hk, yStart, R]
    omega
  apply sum_congr hmem
  intro a _
  have ht : (innerQuad s h E d t).eval a = C.term a t := by
    simp only [C, bankCore, Core.term, P1_7_6_4.Line.at, innerQuad, hk, P1_7_6.Quad.eval_ofLines,
      widthOrigin, yStart, Nat.cast_add]
    ring
  rw [ht]
  rfl
private theorem colEnd_lt (s : Shape) (h t q : ℕ) :
    q < colEnd s h t ↔ q < s.B+1 ∧ 2*h*t+(131071-h)*q < s.m*agreement :=
  lt_linearEnd _ _ _ _ _
private theorem outer_sum (s : Shape) (h E v d l r k : ℕ) (hJ : s.J < 2*h)
    (hk : ∀ t ∈ Ico l r, colEnd s h t = k) :
    (∑ t ∈ Ico l r, outerPart s h E v d t) = if l < r then outerPart s h E v d l else 0 := by
  by_cases hl : l < r
  · rw [ite_eq_left hl]
    have hkl := hk l (mem_Ico.mpr ⟨le_rfl,hl⟩)
    apply sum_eq_single l
    · intro t ht hne
      have hat : l+1 ≤ t := by have := (mem_Ico.mp ht).1; omega
      have hkt := hk t ht
      unfold outerPart
      rw [hkt]
      split
      next hb =>
        have htop : s.m*agreement ≤ 2*h*l+(131071-h)*k := by
          by_contra! hpos
          exact (Nat.lt_irrefl _) (hkl ▸ (colEnd_lt s h l k).mpr ⟨hb,hpos⟩)
        have hstep := Nat.mul_le_mul_left (2*h) hat
        rw [Nat.mul_add, Nat.mul_one] at hstep
        have he : s.J < edgeShift s h t := by unfold edgeShift; rw [hkt]; omega
        have hz : outerEnd s h E v d t (min t (orderEnd s E v-1)+1) ≤ t-s.J :=
          (min_le_left _ _).trans (by omega)
        exact ite_eq_right (not_lt_of_ge hz)
      next => rfl
    · exact fun h => (h (mem_Ico.mpr ⟨le_rfl,hl⟩)).elim
  · simp [hl, Ico_eq_empty_of_le (Nat.le_of_not_gt hl)]
def groupValue (s : Shape) (h E v d l r k : ℕ) : ℤ :=
  if l < r then
    let C := bankCore s h E v d k
    corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l
  else 0
theorem groupValue_eq (s : Shape) (h E v d l r k : ℕ) (hJ : s.J < 2*h)
    (hk : ∀ t ∈ Ico l r, colEnd s h t = k) :
    groupValue s h E v d l r k = 6*(∑ t ∈ Ico l r, phaseBlock s h E v d t) := by
  unfold groupValue
  by_cases hl : l < r
  · rw [ite_eq_left hl]
    let C := bankCore s h E v d k
    change corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l = _
    have hs : (∑ t ∈ Ico l r, phaseBlock s h E v d t) =
        ∑ t ∈ Ico l r, (60*diagonalCore C s.J t + outerPart s h E v d t) :=
      sum_congr rfl fun t ht => diagonal_eq s h E v d t k (hk t ht)
    rw [hs, sum_add_distrib, ← mul_sum, outer_sum s h E v d l r k hJ hk, ite_eq_left hl]
    simp only [corePrefix, Core.prefix_eq, diagonalCore]
    rw [sum_Ico_eq_sub _ hl.le]
    ring
  · simp [hl, Ico_eq_empty_of_le (Nat.le_of_not_gt hl)]
end P3_7_4
end
section
namespace P3_7_4
open P3 (HighBand)
open P3_7 (Bank Grade   terminal)
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (agreement)
open P0_10_5 (Row scan)
open P0_10_5 (scan_sum)
def boundary (s : Shape) (h n i : ℕ) : ℕ :=
  if i = 0 then 0
  else linearEnd ((131071-h)*(s.B+1-i)) (2*h) (s.m*agreement) n
private theorem lt_boundary (s : Shape) (h n i t : ℕ) (hi : 0 < i) (hB : i ≤ s.B+1) :
    t < boundary s h n i ↔ t < n ∧ s.B+1-i < colEnd s h t := by
  have hb : s.B+1-i < s.B+1 := by omega
  simp only [boundary, ite_eq_right (Nat.ne_of_gt hi), colEnd, lt_linearEnd, hb, true_and, add_comm]
private theorem boundary_step (s : Shape) (h n i : ℕ) (hi : i+1 ≤ s.B+1) :
    boundary s h n i ≤ boundary s h n (i+1) := by
  by_cases hz : i = 0
  · simp [hz,boundary]
  by_contra! hn
  let t := boundary s h n (i+1)
  obtain ⟨ht,hk⟩ := (lt_boundary s h n i t (by omega) (by omega)).mp hn
  exact (Nat.lt_irrefl _) ((lt_boundary s h n (i+1) t (by omega) hi).mpr ⟨ht,by omega⟩)
private theorem group_column (s : Shape) (h n i t : ℕ) (hi : i+1 ≤ s.B+1)
    (ht : t ∈ Ico (boundary s h n i) (boundary s h n (i+1))) :
    colEnd s h t = s.B+1-i := by
  obtain ⟨hl,hr⟩ := mem_Ico.mp ht
  obtain ⟨htn,hq⟩ := (lt_boundary s h n (i+1) t (by omega) hi).mp hr
  have hu : colEnd s h t ≤ s.B+1-i := by
    by_contra! hh
    by_cases hz : i = 0
    · subst i
      have he : s.B+1 < colEnd s h t := by simpa using hh
      exact (Nat.lt_irrefl _) ((lt_linearEnd _ _ _ _ _).mp he).1
    · exact (not_lt_of_ge hl) ((lt_boundary s h n i t (by omega) (by omega)).mpr ⟨htn,hh⟩)
  omega
private theorem sum_groups (s : Shape) (h n count : ℕ) (hc : count ≤ s.B+1) (f : ℕ → ℤ) :
    (∑ i ∈ range count, ∑ t ∈ Ico (boundary s h n i) (boundary s h n (i+1)), f t) =
      ∑ t ∈ range (boundary s h n count), f t := by
  induction count with
  | zero => simp [boundary]
  | succ i ih =>
    rw [sum_range_succ, ih (by omega : i ≤ s.B+1), sum_range_add_sum_Ico f (boundary_step s h n i hc)]
def runValue (s : Shape) (h E v n i : ℕ) : ℤ :=
  let l := boundary s h n i
  let r := boundary s h n (i+1)
  let k := s.B+1-i
  groupValue s h E v 0 l r k - groupValue s h E v 1 l r k
def runRow (s : Shape) (h E v n i : ℕ) : Row :=
  ⟨true,runValue s h E v n i,runValue s (h+1) E v n i⟩
private theorem run_sum (s : Shape) (h E v n count : ℕ) (hc : count ≤ s.B+1)
    (hJ : s.J < 2*h) (hb : boundary s h n count = n) :
    (∑ i ∈ range count, runValue s h E v n i) =
      6*(∑ t ∈ range n, (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) := by
  conv_rhs => rw [← hb, ← sum_groups s h n count hc, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hc' : i+1 ≤ s.B+1 := Nat.le_trans (mem_range.mp hi) hc
  have hk := fun t ht => group_column s h n i t hc' ht
  rw [runValue, groupValue_eq _ _ _ _ _ _ _ _ hJ hk,
    groupValue_eq _ _ _ _ _ _ _ _ hJ hk, sum_sub_distrib]
  ring
theorem checks_of_runs (s : Shape) (N P h E v n count : ℕ) (left next cost costNext : ℤ)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hs : scan (runRow s h E v n) 0 count = ⟨true,left,next⟩)
    (hl : 6*scaledDebit s N P h = cost) (hr : 6*scaledDebit s N P (h+1) = costNext)
    (hp : cost < left) (hd : left+costNext ≤ next+cost) :
    BlockChecks s N P h E v := by
  have hbase := scan_sum (runRow s h E v n) 0 count false
  have hnext := scan_sum (runRow s h E v n) 0 count true
  rw [hs] at hbase hnext
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, runRow] at hbase hnext
  rw [run_sum s h E v n count hc hJ hb] at hbase
  rw [run_sum s (h+1) E v n count hc (by omega) hbNext] at hnext
  unfold BlockChecks blockSurplus
  rw [hn]
  omega
end P3_7_4
end
section
namespace P3_7_4
open K1_14 (Shape)
open P0_10_5 (Row scan joinRows)
inductive Parts (f : ℕ → Row) (last : ℕ) : ℕ → ℕ → ℤ → ℤ → Prop
  | final {a : ℕ} {gain next : ℤ} :
      scan f a last = ⟨true, gain, next⟩ → Parts f last a last gain next
  | more {a count : ℕ} {gain next restGain restNext : ℤ} :
      scan f a 16 = ⟨true, gain, next⟩ → Parts f last (a+16) count restGain restNext →
      Parts f last a (16+count) (gain+restGain) (next+restNext)
theorem Parts.scan_eq {f : ℕ → Row} {last a count : ℕ} {gain next : ℤ}
    (parts : Parts f last a count gain next) : scan f a count = ⟨true, gain, next⟩ := by
  induction parts with
  | final h => exact h
  | @more a count gain next restGain restNext h _ ih =>
    exact joinRows a 16 count _ _ h ih rfl
theorem certify {s : Shape} {N P h E v n last count : ℕ}
    {gain next cost costNext : ℤ}
    (parts : Parts (runRow s h E v n) last 0 count gain next)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hl : 6*scaledDebit s N P h = cost) (hr : 6*scaledDebit s N P (h+1) = costNext)
    (hp : cost < gain) (hd : gain+costNext ≤ next+cost) :
    BlockChecks s N P h E v :=
  checks_of_runs s N P h E v n count gain next cost costNext
    hn hc hJ hb hbNext parts.scan_eq hl hr hp hd
end P3_7_4
end
section
namespace P3_7_4
open P0_10_5 (Row)
local notation "S" u => (⟨124,173,32,u⟩ : K1_14.Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 22832869
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
end P3_7_4
end
section
namespace P3_7_4_1
open P0_10_5 (Row)
open P3_7_4 (BlockChecks  Parts certify )
local notation "S" u => (⟨6600,9172,1952,u⟩ : K1_14.Shape)
local notation "N" => 0x1e372113d00000
local notation "P" => 0xae27f29bc6cc
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
end P3_7_4_1
end
section
namespace P3_7_4_2
open P3_7 ( terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks  Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
end P3_7_4_2
end
section
namespace P3_7_4_2
open P3_7 ( terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks  Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
end P3_7_4_2
end
section
namespace P3_7_4_2
open P3_7 ( terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks  Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
end P3_7_4_2
end
section
namespace P3_7_4_2
open P3_7 ( terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks  Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
end P3_7_4_2
end

end Merged6967_GoldBranch7N4

section Merged6967_KoalaRectCutoff
set_option Elab.async false



set_option Elab.async false

-- merged module KoalaRectPosition
section Merged_KoalaRectPosition

-- merged module KoalaRectSource
section Merged_KoalaRectSource

set_option Elab.async false

namespace KoalaRect
noncomputable section
open Polynomial K1_14 K1_14_1 K1_14_1_7
open K1 (I)
open scoped BigOperators
open K1_14_1 (centerCoeff centerCoeff_eval)

def rectShaped {F : Type} [Field F] (U : Fin 2 → ℕ) (P : TrueSource F) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → ∀ z, e z ≤ U z

def seedSupport {F : Type} [Field F] (U : Fin 2 → ℕ) : Submodule F (TrueSource F) where
  carrier := {P | rectShaped U P}
  zero_mem' := by simp [rectShaped, sourceCoeff]
  add_mem' := by
    intro P Q hP hQ j i a e hne z
    by_contra hb
    have hP0 : sourceCoeff P j i a e = 0 := by
      by_contra hz
      exact hb (hP j i a e hz z)
    have hQ0 : sourceCoeff Q j i a e = 0 := by
      by_contra hz
      exact hb (hQ j i a e hz z)
    apply hne
    change ((((P + Q).coeff j).coeff i).coeff a).coeff e = 0
    simp only [Polynomial.coeff_add, AddMonoidAlgebra.coeff_add]
    change sourceCoeff P j i a e + sourceCoeff Q j i a e = 0
    rw [hP0, hQ0, add_zero]
  smul_mem' := by
    intro c P hP j i a e hne z
    apply hP j i a e _ z
    intro hz
    apply hne
    simp [sourceCoeff, Polynomial.coeff_smul, show (((P.coeff j).coeff i).coeff a).coeff e = 0 from hz]

abbrev rectAmbient (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  ambient h s W ⊓ seedSupport U

abbrev rectContacted (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  contacted h word s W ⊓ seedSupport U

abbrev rectComplete {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  complete Crt word s W ⊓ seedSupport U

def rectEvaluated {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule FX Jet :=
  Submodule.span FX (centerEval '' (rectComplete Crt word s W U : Set Source))

theorem rectEvaluated_le {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectEvaluated Crt word s W U ≤ evaluated Crt word s W :=
  Submodule.span_mono (Set.image_mono inf_le_left)

theorem rectEvaluated_axis {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape} {W : ℕ} {U : Fin 2 → ℕ} {P : Jet} (hP : P ∈ rectEvaluated Crt word s W U)
    (j i : ℕ) (z : Fin 2) : ((P.coeff j).coeff i).degreeOf z ≤ U z := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro e he
  by_contra hb
  have hsub : rectEvaluated Crt word s W U ≤ LinearMap.ker (centerCoeff j i e) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply centerCoeff_eval
    intro a
    by_contra hz
    exact hb (hQ.2 j i a e hz z)
  exact (MvPolynomial.mem_support_iff.mp he) (LinearMap.mem_ker.mp (hsub hP))

abbrev AxisIndex (U : Fin 2 → ℕ) := ∀ z : Fin 2, Fin (U z + 1)

def axisExponent {U : Fin 2 → ℕ} (e : AxisIndex U) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => (e z).val)

@[simp] theorem axisExponent_apply {U : Fin 2 → ℕ} (e : AxisIndex U) (z : Fin 2) :
    axisExponent e z = (e z).val := by simp [axisExponent]

def area (U : Fin 2 → ℕ) := (U 0 + 1) * (U 1 + 1)

theorem axis_card (U : Fin 2 → ℕ) : Fintype.card (AxisIndex U) = area U := by
  simp [AxisIndex, Fintype.card_pi, Fin.prod_univ_two, area]

theorem exists_axisIndex {U : Fin 2 → ℕ} (e : Fin 2 →₀ ℕ) (he : ∀ z, e z ≤ U z) :
    ∃ a : AxisIndex U, axisExponent a = e :=
  ⟨fun z => ⟨e z, Nat.lt_succ_of_le (he z)⟩, by ext z; simp⟩

theorem axisExponent_injective (U : Fin 2 → ℕ) : Function.Injective (axisExponent (U := U)) := by
  intro a b h
  funext z
  apply Fin.ext
  simpa using congrArg (fun e : Fin 2 →₀ ℕ => e z) h

open K1_14_1_5 (trueWidth lt_trueWidth_iff trueWidth_eq_add seedWeight_eq Exponents monomialAt coeffAt_monomialAt)

private abbrev RectIndex (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :=
  Σ q : Fin (s.B + 1), Σ j : Fin (min q.val s.J + 1),
    Fin (trueWidth h s W q.val j.val) × AxisIndex U

private def rectExponents {h : ℕ} {s : Shape} {W : ℕ} {U : Fin 2 → ℕ}
    (k : RectIndex h s W U) : Exponents :=
  (k.2.1.val, k.1.val - k.2.1.val, k.2.2.1.val, axisExponent k.2.2.2)

private theorem rectExponents_injective (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Function.Injective (rectExponents (h := h) (s := s) (W := W) (U := U)) := by
  rintro ⟨q, j, a, b⟩ ⟨q', j', a', b'⟩ he
  obtain ⟨hj, hi, ha, hb⟩ : j.val = j'.val ∧ q.val - j.val = q'.val - j'.val ∧
      a.val = a'.val ∧ axisExponent b = axisExponent b' := by simpa [rectExponents] using he
  have hqj := (Nat.le_of_lt_succ j.isLt).trans (min_le_left _ _)
  have hq'j' := (Nat.le_of_lt_succ j'.isLt).trans (min_le_left _ _)
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hje : j = j' := Fin.ext hj
  subst j'
  have hae : a = a' := Fin.ext ha
  subst a'
  have hbe := axisExponent_injective U hb
  subst b'
  rfl

private theorem rectExponents_exists {h : ℕ} {s : Shape} {W j i a : ℕ}
    {U : Fin 2 → ℕ} {e : Fin 2 →₀ ℕ} (hE : trueEligible h s W j i a e)
    (hU : ∀ z, e z ≤ U z) : ∃ k : RectIndex h s W U, rectExponents k = (j, i, a, e) := by
  obtain ⟨hq, hj, _, ha⟩ := hE
  obtain ⟨b, hb⟩ := exists_axisIndex e hU
  let q : Fin (s.B + 1) := ⟨i + j, by omega⟩
  let v : Fin (min q.val s.J + 1) := ⟨j, Nat.lt_succ_of_le (le_min (by dsimp [q]; omega) hj)⟩
  let x : Fin (trueWidth h s W q.val v.val) := ⟨a, (lt_trueWidth_iff h s W _ _ _).mpr ha⟩
  exact ⟨⟨q, v, x, b⟩, by simp [rectExponents, q, v, x, hb]⟩

private def rectMonomial {h : ℕ} {s : Shape} {W : ℕ} {U : Fin 2 → ℕ}
    (hbox : U 0 + U 1 ≤ s.U) (k : RectIndex h s W U) : rectAmbient h s W U := by
  refine ⟨monomialAt (rectExponents k), ?_, ?_⟩
  · intro j i a e he
    rw [coeffAt_monomialAt (rectExponents k) (j,i,a,e), ite_eq_right]
    intro hEq
    apply he
    change trueEligible h s W (j,i,a,e).1 (j,i,a,e).2.1 (j,i,a,e).2.2.1 (j,i,a,e).2.2.2
    rw [← hEq]
    rcases k with ⟨q, v, x, b⟩
    have hq := q.isLt
    have hv := v.isLt
    have hvq := min_le_left q.val s.J
    have hvJ := min_le_right q.val s.J
    have hvq' : q.val - v.val + v.val = q.val := by omega
    have hboxv := Nat.add_le_add (Nat.le_of_lt_succ (b 0).isLt) (Nat.le_of_lt_succ (b 1).isLt)
    simp only [rectExponents, trueEligible, hvq', seedWeight_eq, axisExponent_apply]
    exact ⟨by omega, by omega, hboxv.trans hbox, (lt_trueWidth_iff h s W _ _ _).mp x.isLt⟩
  · intro j i a e hz z
    change coeffAt _ j i a e ≠ 0 at hz
    rw [coeffAt_monomialAt (rectExponents k) (j,i,a,e)] at hz
    split_ifs at hz with he
    · change (j,i,a,e).2.2.2 z ≤ U z
      rw [← he]
      exact Nat.le_of_lt_succ (k.2.2.2 z).isLt
    · exact (hz rfl).elim

private def rectCoordinates (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    rectAmbient h s W U →ₗ[L] (RectIndex h s W U → L) where
  toFun P k := coeffAt P (rectExponents k).1 (rectExponents k).2.1
    (rectExponents k).2.2.1 (rectExponents k).2.2.2
  map_add' P Q := by funext k; simp [coeffAt]
  map_smul' c P := by funext k; simp [coeffAt, Polynomial.coeff_smul]

private def rectCoordinateEquiv (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hbox : U 0 + U 1 ≤ s.U) : rectAmbient h s W U ≃ₗ[L] (RectIndex h s W U → L) := by
  classical
  refine LinearEquiv.ofBijective (rectCoordinates h s W U) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    apply MvPolynomial.ext
    intro e
    change coeffAt P j i a e = coeffAt Q j i a e
    by_cases he : trueEligible h s W j i a e
    · by_cases hb : ∀ z, e z ≤ U z
      · obtain ⟨k, hk⟩ := rectExponents_exists he hb
        have hval := congrFun hPQ k
        change coeffAt P (rectExponents k).1 (rectExponents k).2.1 (rectExponents k).2.2.1
          (rectExponents k).2.2.2 = coeffAt Q (rectExponents k).1 (rectExponents k).2.1
            (rectExponents k).2.2.1 (rectExponents k).2.2.2 at hval
        simpa only [hk] using hval
      · have hzero (R : rectAmbient h s W U) : coeffAt R j i a e = 0 := by
          by_contra hne
          exact hb (R.property.2 j i a e hne)
        rw [hzero P, hzero Q]
    · exact (P.property.1 j i a e he).trans (Q.property.1 j i a e he).symm
  · intro f
    refine ⟨∑ k, f k • rectMonomial hbox k, ?_⟩
    funext d
    have hmono (k : RectIndex h s W U) : rectCoordinates h s W U (rectMonomial hbox k) d =
        if k = d then 1 else 0 := by
      change coeffAt (monomialAt (rectExponents k)) (rectExponents d).1 (rectExponents d).2.1
        (rectExponents d).2.2.1 (rectExponents d).2.2.2 = _
      simp only [coeffAt_monomialAt, (rectExponents_injective h s W U).eq_iff]
    rw [map_sum]
    simp [Finset.sum_apply, hmono, mul_ite]

theorem rectAmbient_finrank (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hbox : U 0 + U 1 ≤ s.U) :
    Module.finrank L (rectAmbient h s W U) = area U * shapeSum s (trueWidth h s W) := by
  rw [(rectCoordinateEquiv h s W U hbox).finrank_eq, Module.finrank_pi]
  unfold RectIndex shapeSum
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, axis_card, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact Nat.mul_comm _ _

end
end KoalaRect

end Merged_KoalaRectSource

-- merged module KoalaRectCharge
section Merged_KoalaRectCharge

namespace KoalaRect
open K1_14 (Shape shapeSum)

def rectSlots (U d : Fin 2 → ℕ) (r : ℕ) : ℕ :=
  (U 0 + 1 - r*d 0) * (U 1 + 1 - r*d 1)

def rectGain (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*A+j - q*(131071-h)
    let c := rectSlots U d
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

def rectDebit (h nodes moment : ℕ) (U : Fin 2 → ℕ) : ℕ :=
  area U * nodes + h*(U 0+U 1+2)*moment

theorem rectSlots_zero (U d : Fin 2 → ℕ) : rectSlots U d 0 = area U := by
  simp [rectSlots, area]

theorem rectSlots_antitone (U d : Fin 2 → ℕ) : Antitone (rectSlots U d) :=
  fun _ _ h => Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _)
    (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _)

end KoalaRect

end Merged_KoalaRectCharge

-- merged module KoalaRectPosition
section Merged_KoalaRectPosition

set_option Elab.async false

namespace KoalaRect
open Finset
open K1_14 (Shape shapeSum)
open K1_14_4 (gradeWidth)
open scoped BigOperators
open K1_14_4 (sum_slot_drops sum_interval power_threshold shapeSum_swap)

def rectPower (A h : ℕ) (s : Shape) (W : ℕ) : ℕ := 1 + (s.m*A-1-W)/(2*h)

def rectKept (U d : Fin 2 → ℕ) (g r : ℕ) : ℕ := if r ≤ g then rectSlots U d r else 0

def rectCapacity (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then rectKept U d ((q-j)/E) (rectPower A h s W-j) else 0

def rectGrade (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W j : ℕ) : ℕ :=
  let r := rectPower A h s W-j
  (gradeWidth (131071-h) s.B W j-r*E)*rectSlots U d r

private theorem rectGrade_sum (k B W j r E : ℕ) (U d : Fin 2 → ℕ) (hk : 0 < k) (he : 0 < E) :
    (gradeWidth k B W j-r*E)*rectSlots U d r =
      ∑ q ∈ Ico j (B+1), if q*k ≤ W+j then rectKept U d ((q-j)/E) r else 0 := by
  have hq (q : ℕ) : q*k ≤ W+j ↔ q < (W+j)/k + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk]
  have hr (q : ℕ) : r ≤ (q-j)/E ↔ r*E ≤ q-j := Nat.le_div_iff_mul_le he
  have hI : (Ico j (B+1)).filter (fun q => q*k ≤ W+j ∧ r ≤ (q-j)/E) =
      Ico (j+r*E) (min (B+1) ((W+j)/k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, hq, hr, lt_min_iff]
    omega
  simp_rw [rectKept, ← ite_and]
  rw [← sum_filter, hI, sum_const, Nat.nsmul_eq_mul, Nat.card_Ico, gradeWidth, Nat.sub_sub]

theorem rectCapacity_eq (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), rectGrade A h s E U d W j) = rectCapacity A h s E U d W := by
  rw [rectCapacity, ← shapeSum_swap]
  exact sum_congr rfl fun j _ => rectGrade_sum _ _ _ _ _ _ _ _ hk he

private theorem rectPosition_sum (top step t j g : ℕ) (U d : Fin 2 → ℕ)
    (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then rectKept U d g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (rectSlots U d a - rectSlots U d (a+1)) * (top+j-t-step*(j+a))) +
      rectSlots U d g * (top+j-t-step*(j+g))) =
    area U * (top+j-t) := by
  let C := rectKept U d g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone C := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [C, rectKept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        rectSlots_antitone U d hab
    · simp [C, rectKept, hb]
  have hmin (l : ℕ) : C (min (g+1) l) = C l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [C, rectKept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (C a - C (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (rectSlots U d a - rectSlots U d (a+1)) * (top+j-t-step*(j+a))) +
        rectSlots U d g * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [C, rectKept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [C, rectKept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then C (L W) else 0) + _ = _
  have hzero : C 0 = area U := by simp [C, rectKept, rectSlots_zero]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (C 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops C hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]

theorem rectCapacity_total (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ)
    (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*A), rectCapacity A h s E U d W) + rectGain A h s E U d =
      area U * shapeSum s (fun q j => s.m*A+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*A), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*A), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [rectCapacity, rectGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact rectPosition_sum (s.m*A) (2*h) (q*(131071-h)) j ((q-j)/E) U d (hjq.trans hq) hh

#print axioms rectCapacity_total
end KoalaRect

end Merged_KoalaRectPosition

end Merged_KoalaRectPosition

-- merged module KoalaRectCutoff
section Merged_KoalaRectCutoff

-- merged module KoalaRectQuotient
section Merged_KoalaRectQuotient

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section

open Polynomial MvPolynomial
open K1_14 (FX Equation)
open Cardinal
open K1_14_4 (seedView seedView_coeff flatten)

/-- Degree in one seed coordinate with the ordinate kept in the coefficient ring. -/
def axisDegree (f : Equation) (z : Fin 2) : ℕ := (seedView f).degreeOf z

theorem axisDegree_le_iff (f : Equation) (z : Fin 2) (u : ℕ) :
    axisDegree f z ≤ u ↔ ∀ i : ℕ, (f.coeff i).degreeOf z ≤ u := by
  unfold axisDegree
  constructor
  · intro h i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hs : d ∈ (seedView f).support := by
      rw [MvPolynomial.mem_support_iff] at hd ⊢
      intro hz
      apply hd
      rw [← seedView_coeff, hz, Polynomial.coeff_zero]
    exact (MvPolynomial.degreeOf_le_iff.mp h) d hs
  · intro h
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
    apply (MvPolynomial.degreeOf_le_iff.mp (h i)) d
    rwa [MvPolynomial.mem_support_iff, ← seedView_coeff, ← Polynomial.mem_support_iff]

theorem axisDegree_mul {f g : Equation} (hf : f ≠ 0) (hg : g ≠ 0) (z : Fin 2) :
    axisDegree (f * g) z = axisDegree f z + axisDegree g z := by
  unfold axisDegree
  rw [map_mul, MvPolynomial.degreeOf_mul_eq (by simpa using hf) (by simpa using hg)]

theorem axisDegree_pow {f : Equation} (hf : f ≠ 0) (n : ℕ) (z : Fin 2) :
    axisDegree (f ^ n) z = n * axisDegree f z := by
  induction n with
  | zero => simp [axisDegree]
  | succ n ih => rw [pow_succ, axisDegree_mul (pow_ne_zero _ hf) hf, ih, Nat.succ_mul]

private abbrev QuotientSlots (a : ℕ) (u : Fin 2 → ℕ) := Fin a × (∀ z : Fin 2, Fin (u z))

private def quotientExponent {a : ℕ} {u : Fin 2 → ℕ} (k : QuotientSlots a u) :
    Option (Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => z.elim k.1.val (fun i => (k.2 i).val))

private def quotientSupport (a : ℕ) (u : Fin 2 → ℕ) : Finset (Option (Fin 2) →₀ ℕ) :=
  Finset.univ.image (quotientExponent (a := a) (u := u))

private theorem flatten_mem_quotientSupport {q : Equation} {a : ℕ} {u : Fin 2 → ℕ}
    (hy : q.natDegree < a) (hu : ∀ z, axisDegree q z < u z) :
    flatten q ∈ restrictSupport FX (↑(quotientSupport a u) : Set (Option (Fin 2) →₀ ℕ)) := by
  apply (MvPolynomial.mem_restrictSupport_iff FX).mpr
  intro m hm
  have hc : ((seedView q).coeff m.some).coeff (m none) ≠ 0 := by
    change ((optionEquivRight FX (Fin 2) (flatten q)).coeff m.some).coeff (m none) ≠ 0
    rw [optionEquivRight_coeff_coeff, Finsupp.optionElim_some]
    exact MvPolynomial.mem_support_iff.mp hm
  have hs : m.some ∈ (seedView q).support :=
    MvPolynomial.mem_support_iff.mpr (fun hz => hc (by rw [hz, Polynomial.coeff_zero]))
  have hq : (q.coeff (m none)).coeff m.some ≠ 0 := by rwa [← seedView_coeff]
  have hmY : m none < a := (Polynomial.le_natDegree_of_ne_zero (fun hz => hq (by simp [hz]))).trans_lt hy
  have hmU (z : Fin 2) : m (some z) < u z :=
    (MvPolynomial.le_degreeOf_of_mem_support z hs).trans_lt (hu z)
  let k : QuotientSlots a u := ⟨⟨m none, hmY⟩, fun z => ⟨m (some z), hmU z⟩⟩
  change m ∈ quotientSupport a u
  refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
  ext z
  cases z <;> simp [quotientExponent, k]

/-- Dividing by `g` spends the ordinate degree and the two seed degrees independently. -/
theorem rank_rect_multiples_le (C : Submodule FX Equation) {g : Equation} (hg : g ≠ 0)
    {a yspent : ℕ} {U spent : Fin 2 → ℕ} (hyspent : yspent ≤ g.natDegree)
    (hspent : ∀ z, spent z ≤ axisDegree g z)
    (hC : ∀ c ∈ C, c ≠ 0 → c.natDegree < a ∧
      (∀ i z, (c.coeff i).degreeOf z ≤ U z) ∧ g ∣ c) :
    Module.rank FX C ≤ (↑((a - yspent) * (U 0 + 1 - spent 0) * (U 1 + 1 - spent 1)) : Cardinal) := by
  classical
  let u (z : Fin 2) := U z + 1 - spent z
  let S := quotientSupport (a - yspent) u
  let B := restrictSupport FX (↑S : Set (Option (Fin 2) →₀ ℕ))
  let _ : Module.Finite FX B := restrictSupport_finite S.finite_toSet
  let m : B →ₗ[FX] Equation :=
    (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
  have hm : C ≤ LinearMap.range m := by
    intro c hc
    by_cases hn : c = 0
    · rw [hn]
      exact (LinearMap.range m).zero_mem
    · obtain ⟨hY, hU, q, rfl⟩ := hC c hc hn
      have hq : q ≠ 0 := right_ne_zero_of_mul hn
      have hqY : q.natDegree < a - yspent := by
        rw [Polynomial.natDegree_mul hg hq] at hY
        omega
      have hqU (z : Fin 2) : axisDegree q z < u z := by
        have hu := (axisDegree_le_iff (g * q) z (U z)).mpr (fun i => hU i z)
        rw [axisDegree_mul hg hq] at hu
        have hs := hspent z
        dsimp [u]
        omega
      refine ⟨⟨flatten q, flatten_mem_quotientSupport hqY hqU⟩, ?_⟩
      change g * flatten.symm (flatten q) = g * q
      rw [AlgEquiv.symm_apply_apply]
  have hB : Module.finrank FX B ≤ (a - yspent) * (U 0 + 1 - spent 0) * (U 1 + 1 - spent 1) := by
    rw [MvPolynomial.finrank_restrictSupport_finset]
    calc
      S.card ≤ Fintype.card (QuotientSlots (a - yspent) u) := by
        simpa only [S, quotientSupport, Finset.card_univ] using
          (Finset.card_image_le (s := (Finset.univ : Finset (QuotientSlots (a - yspent) u)))
            (f := quotientExponent))
      _ = _ := by
        simp only [QuotientSlots, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Fin.prod_univ_two, u]
        rw [Nat.mul_assoc]
  calc
    _ ≤ Module.rank FX (LinearMap.range m) := Submodule.rank_mono hm
    _ ≤ Module.rank FX B := rank_range_le m
    _ ≤ _ := by rw [← Module.finrank_eq_rank]; exact_mod_cast hB

#print axioms axisDegree_pow
#print axioms rank_rect_multiples_le

end
end KoalaRect

end Merged_KoalaRectQuotient

-- merged module KoalaRectCutoff
section Merged_KoalaRectCutoff

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section
open Finset Polynomial
open K1_14 (FX Jet Equation Shape)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth)
open K1_14_4 (gradeMap mem_filtered finrank_le_grades)
open scoped BigOperators

/-- Grade capacity for an independently prescribed physical window and
residual contact order. These can both decrease after graph division. -/
theorem rectContact_finrank_le (step B J k E W : ℕ) (U d : Fin 2 → ℕ)
    (V : Submodule FX Jet) {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree)
    (hk : 0 < step)
    (hrow : ∀ {P : Jet}, P ∈ V → P ≠ 0 →
      P.leadingCoeff.natDegree + P.natDegree ≤ B ∧ P.natDegree ≤ J)
    (haxis : ∀ P ∈ V, ∀ j i z, ((P.coeff j).coeff i).degreeOf z ≤ U z)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree)*step ≤ W+P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (k-P.natDegree) ∣ P.leadingCoeff)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    Module.finrank FX V ≤ ∑ j∈range (J+1),
      (gradeWidth step B W j-(k-j)*E)*rectSlots U d (k-j) := by
  refine finrank_le_grades (F := FX) (A := Equation) V (fun j=>(gradeWidth step B W j - (k-j)*E)*rectSlots U d (k-j))
    (J+1) ?_ ?_
  · intro j
    let r := k-j
    have hmul := rank_rect_multiples_le (gradeMap (F := FX) (A := Equation) V j).range
      (g := f^r) (pow_ne_zero r hf)
      (a := gradeWidth step B W j) (yspent := r*E)
      (U := U) (spent := fun z => r*axisDegree f z)
      (by rw [Polynomial.natDegree_pow]; exact Nat.mul_le_mul_left _ hE)
      (fun z => by rw [axisDegree_pow hf]) ?_
    · apply hmul.trans
      rw [Nat.mul_assoc]
      change (↑((gradeWidth step B W j-r*E)*rectSlots U (axisDegree f) r) : Cardinal) ≤
        ↑((gradeWidth step B W j-r*E)*rectSlots U d r)
      exact_mod_cast Nat.mul_le_mul_left (gradeWidth step B W j-r*E) (hslots r)
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB, _⟩ := hrow hpV hn
      have hwidth := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ (∀ i z, ((P.coeff j).coeff i).degreeOf z ≤ U z) ∧
        f^r ∣ P.coeff j
      refine ⟨?_, haxis P hpV j, ?_⟩
      · rw [← hj, coeff_natDegree, hj]
        have hle := (Nat.le_div_iff_mul_le hk).2 hwidth
        unfold gradeWidth
        omega
      · rwa [← hj, coeff_natDegree]
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2)

theorem rectCutoff_finrank_le (A h : ℕ) (s : Shape) (E W : ℕ) (U d : Fin 2 → ℕ)
    (V : Submodule FX Jet) {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree)
    (hk : 0 < 131071-h) (he : 0 < E)
    (hsupport : ∀ P ∈ V, RowCaps P s)
    (haxis : ∀ P ∈ V, ∀ j i z, ((P.coeff j).coeff i).degreeOf z ≤ U z)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (rectPower A h s W-P.natDegree) ∣ P.leadingCoeff)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    Module.finrank FX V ≤ rectCapacity A h s E U d W := by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J := by
    have hn' : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    exact ⟨(hsupport P hP _ _ hn').1, (hsupport P hP _ _ hn').2.1⟩
  rw [← rectCapacity_eq _ _ _ _ _ _ _ hk he]
  exact rectContact_finrank_le _ _ _ _ _ _ U d V hf hE hk hrow haxis hlead hdvd hslots

#print axioms rectCutoff_finrank_le
end
end KoalaRect

end Merged_KoalaRectCutoff

end Merged_KoalaRectCutoff

end Merged6967_KoalaRectCutoff

section Merged6967_KoalaRectPoleBalance
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRectPole
noncomputable section

open Polynomial
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open scoped BigOperators Polynomial
open K1_14_1_7_3 (deriv_eval_ne_zero other_eval_ne_zero constant_eval_ne_zero generic_den generic_centre)

/-- Each generic pole block can be indexed by its seed coordinate and one of `h` roots. -/
def Balanced {F : Type} [Field F] {h : ℕ} {H : (Polynomial F)} {lift : (Polynomial (SeedFrac F))}
    (G : SimplePoles h H lift) : Prop :=
  ∃ e : Fin (2*h) ≃ Fin 2 × Fin h, ∀ t, G.side t = (e t).1

private theorem balanced_simple_poles {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p) (D : PoleData h)
    (lift : (Polynomial (SeedFrac GenericField)))
    (hcentre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      lift.eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α)) :
    ∃ G : SimplePoles h ((movingProduct D).map genericPoint) lift, Balanced G := by
  classical
  let H := (movingProduct D).map genericPoint
  have hblocks : H = genericBlock D 0 * genericBlock D 1 := by
    simp only [H, movingProduct, Polynomial.map_mul]
  have hmonic (i : Fin 2) : (genericBlock D i).Monic := (movingBlock_degree hlo D i).monic.map _
  have hdegree (i : Fin 2) : (genericBlock D i).natDegree = h :=
    ((movingBlock_degree hlo D i).monic.natDegree_map _).trans (movingBlock_degree hlo D i).natDegree_eq
  have hsep (i : Fin 2) : (genericBlock D i).Separable := by
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed GenericField GenericField _ _).mpr
    intro α
    by_cases he : (genericBlock D i).eval α = 0
    · exact Or.inr (by simpa using deriv_eval_ne_zero hlo hhi D i he)
    · exact Or.inl (by simpa using he)
  let roots (i : Fin 2) := (genericBlock D i).roots.toFinset
  have hcard (i : Fin 2) : Fintype.card (roots i) = h := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots (hsep i)),
      ← (IsAlgClosed.splits (genericBlock D i)).natDegree_eq_card_roots, hdegree]
  let e (i : Fin 2) : Fin h ≃ ↥(roots i) := (Fintype.equivFinOfCardEq (hcard i)).symm
  let α (i : Fin 2) (k : Fin h) : GenericField := (e i k).val
  have hroot (i : Fin 2) (k : Fin h) : (genericBlock D i).eval (α i k) = 0 :=
    (mem_roots (hmonic i).ne_zero).mp (Multiset.mem_toFinset.mp (e i k).property)
  let index : Fin (2*h) ≃ Fin 2 × Fin h := finProdFinEquiv.symm
  let side (t : Fin (2*h)) := (index t).1
  let root (t : Fin (2*h)) := α (side t) (index t).2
  have hinj : Function.Injective root := by
    intro t u htu
    apply index.injective
    have hs : side t = side u := by
      by_contra hne
      have he : side u = otherBlock (side t) := by
        generalize side t = i at hne ⊢
        generalize side u = j at hne ⊢
        fin_cases i <;> fin_cases j <;> simp_all [otherBlock]
      have ht := other_eval_ne_zero hlo D (side t) (hroot (side t) (index t).2)
      change (genericBlock D (otherBlock (side t))).eval (root t) ≠ 0 at ht
      rw [htu, ← he] at ht
      exact ht (hroot (side u) (index u).2)
    refine Prod.ext hs ?_
    apply (e (side t)).injective
    apply Subtype.ext
    change α (side t) (index t).2 = α (side t) (index u).2
    exact htu.trans (by change α (side u) (index u).2 = _; rw [hs])
  have hprod (i : Fin 2) : genericBlock D i = ∏ k, (Polynomial.X - C (α i k)) := by
    rw [(e i).prod_comp (fun x => Polynomial.X - C x.val)]
    rw [Finset.prod_coe_sort (roots i) (fun x => Polynomial.X - C x)]
    have he : (roots i).val = (genericBlock D i).roots :=
      (Multiset.toFinset_val _).trans (nodup_roots (hsep i)).dedup
    simpa only [Finset.prod, he] using (IsAlgClosed.splits (genericBlock D i)).eq_prod_roots_of_monic (hmonic i)
  have hvan (t : Fin (2*h)) : H.eval (root t) = 0 := by
    have he := hroot (side t) (index t).2
    change (genericBlock D (side t)).eval (root t) = 0 at he
    rw [hblocks, eval_mul]
    rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) (side t) with hz | hz
    · rw [hz] at he
      rw [he, zero_mul]
    · rw [hz] at he
      rw [he, mul_zero]
  have hsimple (t : Fin (2*h)) : H.derivative.eval (root t) ≠ 0 := by
    have he := hroot (side t) (index t).2
    change (genericBlock D (side t)).eval (root t) = 0 at he
    have hn := deriv_eval_ne_zero hlo hhi D (side t) he
    have ho := other_eval_ne_zero hlo D (side t) he
    rw [hblocks, derivative_mul, eval_add, eval_mul, eval_mul]
    rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) (side t) with hz | hz
    · rw [hz] at he hn ho
      change (genericBlock D 1).eval (root t) ≠ 0 at ho
      rw [he, zero_mul, add_zero]
      exact mul_ne_zero hn ho
    · rw [hz] at he hn ho
      change (genericBlock D 0).eval (root t) ≠ 0 at ho
      rw [he, mul_zero, zero_add]
      exact mul_ne_zero ho hn
  have hfac : H = ∏ t, (Polynomial.X - C (root t)) := by
    have h2 : ∏ t, ((Polynomial.X : Polynomial GenericField) - C (root t)) =
        ∏ p : Fin 2 × Fin h, ((Polynomial.X : Polynomial GenericField) - C (α p.1 p.2)) :=
      Fintype.prod_equiv index _ _ (fun t => rfl)
    rw [h2, Fintype.prod_prod_type, Fin.prod_univ_two, hblocks, hprod 0, hprod 1]
    try rfl
  let G : SimplePoles h H lift := {
    root := root
    side := side
    a := fun t => -((D.offset (side t)).map constGeneric).eval (root t)
    b := fun t => ((D.constant (side t)).map constGeneric).eval (root t)
    c := fun t => ((D.slope (side t)).map constGeneric).eval (root t)
    distinct := hinj
    factorization := hfac
    vanishes := hvan
    simple := hsimple
    b_ne := fun t => constant_eval_ne_zero hlo D (side t) (hroot (side t) (index t).2)
    centre := fun t => hcentre _ _ (hroot (side t) (index t).2)
      (constant_eval_ne_zero hlo D (side t) (hroot (side t) (index t).2)) }
  exact ⟨G, index, fun _ => rfl⟩

theorem balanced_deformation {h : ℕ} (hh : 0 < h) (hp : h < K1.p)
    (D : PoleData h) (Crt : CRTLift D) :
    ∃ E : RegularDeformation D Crt, Balanced E.genericPoles := by
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hden : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic : (movingProduct D).Monic :=
    (movingBlock_degree hh D 0).monic.mul (movingBlock_degree hh D 1).monic
  obtain ⟨G, hG⟩ := balanced_simple_poles hh hp D (liftAt genericPoint num den) (by
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb)
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, G⟩, hG⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]

#print axioms balanced_deformation

end
end KoalaRectPole

end Merged6967_KoalaRectPoleBalance

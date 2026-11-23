import ProximityPrize.SubmissionLower.FadicCount

/-!
# The f-adic gate space

For a nonzero polynomial `f` in four jet variables over a field, with weighted degrees in
`[bl, bh]` (grade) and `[jl, jh]` (index), and a slope `(σb, σj, σt)`, the space of level `r` is

    U = ∑_{3a ≤ r} f ^ a • C a,

where `C a` is a complement of the multiples of `f` inside the monomial space of the tapered
box of depth `a`.  `exists_fadicSpace` gives

* `U ≤ restrictSupport 𝕜 TaperColumns.jetExponents` (the accepted `Shared50ShapeRank.ambient`);
* `fadicDim σb σj σt bl bh jl jh r ≤ finrank U`, an explicit sum of accepted `cappedCount`s,
  uniform over the rectangle of weights;
* every nonzero `v ∈ U` is `f ^ a * (c + f * h)` with `3 a ≤ r`, `a < r`, `c ≠ 0`, `¬ f ∣ c`
  and `c` supported in the box `(r - a) • σ`.

Nothing here depends on the geometry modules; the only project imports are
`PrimaryTaperColumns` (the source) and, through it, `Fast068` (the column counts).
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents)
open MvPolynomial
open scoped BigOperators
open Finset

/-! ### Weights of jet exponents -/

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

/-! ### The boxes of one depth -/


/-- The depths used at level `r`. -/
def DepthOK (xb xj r a : ℕ) : Prop :=
  3 * a ≤ r ∧ a < r ∧ a * xb ≤ 4012 ∧ a * xj ≤ 1650 ∧ a * (26 * xb + 25 * xj) ≤ 131312

instance (xb xj r a : ℕ) : Decidable (DepthOK xb xj r a) := by unfold DepthOK; infer_instance






/-! ### One depth -/


/-! ### The direct sum over the depths -/

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


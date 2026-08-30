import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.W2

/- Residual-order estimates used by the submitted candidate. No polynomial
   dimension bound is asserted here without its stated hypotheses. -/
namespace ProximityPrize.SubmissionLower.ResidualOrderMoments
open scoped BigOperators

theorem order_le_residual_add (a j : ℕ) : a ≤ a - j + j := by omega

theorem sum_order_le_residual_add
    {I : Type*} (nodes : Finset I) (mu : I → ℕ) (j : ℕ) :
    (∑ i ∈ nodes, mu i) ≤ (∑ i ∈ nodes, (mu i - j)) + nodes.card * j := by
  calc
    (∑ i ∈ nodes, mu i) ≤ ∑ i ∈ nodes, (mu i - j + j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact order_le_residual_add (mu i) j
    _ = (∑ i ∈ nodes, (mu i - j)) + nodes.card * j := by
      simp [Finset.sum_add_distrib]

/- The remaining input is local root divisibility of the specialized R
   derivative. This lemma does not assert that divisibility automatically. -/
theorem mass_of_regular_polynomial
    {K : Type*} [Field K] [DecidableEq K]
    (nodes selected : Finset K) (nu : K → ℕ)
    (m w A d D gap : ℕ) (P : Polynomial K)
    (hP : P ≠ 0) (hsub : selected ⊆ nodes) (hA : A ≤ selected.card)
    (hm : 1 ≤ m) (hD : D + d = m * A) (hgap : A = w + gap)
    (hdegree : P.natDegree + w ≤ d + 1)
    (hroot : ∀ x ∈ selected, (Polynomial.X - Polynomial.C x) ^ (nu x - 1) ∣ P) :
    D ≤ (∑ x ∈ nodes, (m - nu x)) + gap + 1 := by
  have hlocal (x : K) (hx : x ∈ selected) :
      m - 1 ≤ (m - nu x) + P.rootMultiplicity x := by
    have hr : nu x - 1 ≤ P.rootMultiplicity x :=
      (Polynomial.le_rootMultiplicity_iff hP).mpr (hroot x hx)
    omega
  have hsum : selected.card * (m - 1) ≤
      (∑ x ∈ selected, (m - nu x)) + P.natDegree := by
    calc
      _ = ∑ x ∈ selected, (m - 1) := by simp
      _ ≤ ∑ x ∈ selected, ((m - nu x) + P.rootMultiplicity x) :=
        Finset.sum_le_sum hlocal
      _ = (∑ x ∈ selected, (m - nu x)) +
          ∑ x ∈ selected, P.rootMultiplicity x := by
        rw [Finset.sum_add_distrib]
      _ ≤ _ := Nat.add_le_add_left
        (RCN355.sum_rootMultiplicity_le_natDegree P selected) _
  have hmon : (∑ x ∈ selected, (m - nu x)) ≤
      ∑ x ∈ nodes, (m - nu x) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)
  have hcard := Nat.mul_le_mul_right (m - 1) hA
  have hmul : m * A = A * (m - 1) + A := by
    calc
      m * A = (m - 1 + 1) * A := by rw [Nat.sub_add_cancel hm]
      _ = A * (m - 1) + A := by ring
  omega

/-- Indexed version for the actual IRS domain. Injectivity is used exactly
    once, when mapping the selected indices to distinct roots of P. -/
theorem mass_of_regular_polynomial_indexed
    {K I : Type*} [Field K] [DecidableEq K] [Fintype I]
    (nodes : I ↪ K) (selected : Finset I) (nu : I → ℕ)
    (m w A d D gap : ℕ) (P : Polynomial K)
    (hP : P ≠ 0) (hA : A ≤ selected.card)
    (hm : 1 ≤ m) (hD : D + d = m * A) (hgap : A = w + gap)
    (hdegree : P.natDegree + w ≤ d + 1)
    (hroot : ∀ i ∈ selected, (Polynomial.X - Polynomial.C (nodes i)) ^ (nu i - 1) ∣ P) :
    D ≤ (∑ i : I, (m - nu i)) + gap + 1 := by
  classical
  have hroots : (∑ i ∈ selected, P.rootMultiplicity (nodes i)) ≤ P.natDegree := by
    simpa only [Finset.sum_map] using
      RCN355.sum_rootMultiplicity_le_natDegree P (selected.map nodes)
  have hlocal (i : I) (hi : i ∈ selected) :
      m - 1 ≤ (m - nu i) + P.rootMultiplicity (nodes i) := by
    have hr : nu i - 1 ≤ P.rootMultiplicity (nodes i) :=
      (Polynomial.le_rootMultiplicity_iff hP).mpr (hroot i hi)
    omega
  have hsum : selected.card * (m - 1) ≤
      (∑ i ∈ selected, (m - nu i)) + P.natDegree := by
    calc
      _ = ∑ i ∈ selected, (m - 1) := by simp
      _ ≤ ∑ i ∈ selected, ((m - nu i) + P.rootMultiplicity (nodes i)) :=
        Finset.sum_le_sum hlocal
      _ = (∑ i ∈ selected, (m - nu i)) +
          ∑ i ∈ selected, P.rootMultiplicity (nodes i) := by
        rw [Finset.sum_add_distrib]
      _ ≤ _ := Nat.add_le_add_left hroots _
  have hmon : (∑ i ∈ selected, (m - nu i)) ≤ ∑ i : I, (m - nu i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected) (by intros; omega)
  have hcard := Nat.mul_le_mul_right (m - 1) hA
  have hmul : m * A = A * (m - 1) + A := by
    calc
      m * A = (m - 1 + 1) * A := by rw [Nat.sub_add_cancel hm]
      _ = A * (m - 1) + A := by ring
  omega

theorem remaining_width_le
    (D w n gap j omegaJ : ℕ) (hwn : w ≤ n)
    (hmass : D ≤ omegaJ + n * j + gap + 1) :
    D - w * j - omegaJ ≤ min (D - w * j) (gap + 1 + j * (n - w)) := by
  apply Nat.le_min_of_le_of_le
  · exact Nat.sub_le _ _
  · have hn : n = w + (n - w) := by omega
    have hprod : n * j = w * j + j * (n - w) := by
      conv_lhs => rw [hn]
      rw [Nat.add_mul, Nat.mul_comm (n - w) j]
    omega

theorem remaining_width_of_order_mass
    {I : Type*} (nodes : Finset I) (mu : I → ℕ)
    (D w gap j : ℕ) (hwn : w ≤ nodes.card)
    (hmass : D ≤ (∑ i ∈ nodes, mu i) + gap + 1) :
    D - w * j - (∑ i ∈ nodes, (mu i - j)) ≤
      min (D - w * j) (gap + 1 + j * (nodes.card - w)) := by
  apply remaining_width_le D w nodes.card gap j _ hwn
  have hsum := sum_order_le_residual_add nodes mu j
  omega

theorem footprint_sum_le
    {I : Type*} (nodes : Finset I) (mu : I → ℕ)
    (D w gap L cutoff : ℕ) (hwn : w ≤ nodes.card)
    (hmass : D ≤ (∑ i ∈ nodes, mu i) + gap + 1) :
    (∑ j ∈ Finset.range cutoff,
      (D - w * j - (∑ i ∈ nodes, (mu i - j))) * (L + 1 - j)) ≤
    ∑ j ∈ Finset.range cutoff,
      min (D - w * j) (gap + 1 + j * (nodes.card - w)) * (L + 1 - j) := by
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_right (L + 1 - j)
    (remaining_width_of_order_mass nodes mu D w gap j hwn hmass)

end ProximityPrize.SubmissionLower.ResidualOrderMoments

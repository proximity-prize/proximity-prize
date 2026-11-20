import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring



namespace ProximityPrize.SubmissionLower.Koala6831Quotient

open scoped BigOperators

section Dimension

variable {K : Type*} [Field K] {I : Type*} [Fintype I]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {J U : I → Type*}
variable [∀ i, AddCommGroup (J i)] [∀ i, Module K (J i)] [∀ i, Module.Finite K (J i)]
variable [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]

theorem exists_relative_interpolant
    (globalMultiples : Submodule K V)
    (germ : ∀ i, V →ₗ[K] J i)
    (multiplier : ∀ i, U i →ₗ[K] J i)
    (injective_multiplier : ∀ i, Function.Injective (multiplier i))
    (dimension_gate : Module.finrank K globalMultiples +
      (∑ i, (Module.finrank K (J i) - Module.finrank K (U i))) < Module.finrank K V) :
    ∃ Q : V, Q ∉ globalMultiples ∧ ∀ i, germ i Q ∈ (multiplier i).range := by
  classical
  let constraints : V →ₗ[K] ((i : I) → (J i) ⧸ (multiplier i).range) :=
    LinearMap.pi fun i => (multiplier i).range.mkQ.comp (germ i)
  have target_dimension :
      Module.finrank K ((i : I) → (J i) ⧸ (multiplier i).range) =
        ∑ i, (Module.finrank K (J i) - Module.finrank K (U i)) := by
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro i _
    have dimension := (multiplier i).range.finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj (injective_multiplier i)] at dimension
    omega
  have range_le : Module.finrank K constraints.range ≤
      ∑ i, (Module.finrank K (J i) - Module.finrank K (U i)) :=
    constraints.range.finrank_le.trans_eq target_dimension
  have rank_nullity := constraints.finrank_range_add_finrank_ker
  have ker_not_le : ¬ constraints.ker ≤ globalMultiples := by
    intro included
    have ker_le := Submodule.finrank_mono included
    omega
  have exists_proper : ∃ Q : V, Q ∈ constraints.ker ∧ Q ∉ globalMultiples := by
    by_contra no_proper
    apply ker_not_le
    intro Q Q_ker
    by_contra Q_proper
    exact no_proper ⟨Q, Q_ker, Q_proper⟩
  obtain ⟨Q, Q_ker, Q_proper⟩ := exists_proper
  refine ⟨Q, Q_proper, fun i => ?_⟩
  have vanishes := congrFun (LinearMap.mem_ker.mp Q_ker) i
  change (multiplier i).range.mkQ (germ i Q) = 0 at vanishes
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at vanishes

end Dimension

section LocalMultiplication

variable {A : Type*} [CommRing A] [IsDomain A]

theorem local_multiplier_injective (m : ℕ) {q P R : Polynomial A}
    (q_ne : q ≠ 0) (q_order : q.natTrailingDegree = 1)
    (P_degree : P.degree < (↑(m - 1) : WithBot ℕ))
    (R_degree : R.degree < (↑(m - 1) : WithBot ℕ))
    (same_truncation : Polynomial.X ^ m ∣ q * P - q * R) : P = R := by
  by_contra different
  have diff_ne : P - R ≠ 0 := sub_ne_zero.mpr different
  have diff_degree : (P - R).natDegree < m - 1 :=
    (Polynomial.natDegree_lt_iff_degree_lt diff_ne).mpr
      ((Polynomial.degree_sub_le P R).trans_lt (max_lt P_degree R_degree))
  have order_lt : (q * (P - R)).natTrailingDegree < m := by
    rw [Polynomial.natTrailingDegree_mul q_ne diff_ne, q_order]
    have := Polynomial.natTrailingDegree_le_natDegree (P - R)
    omega
  rw [← mul_sub] at same_truncation
  have zero_coeff := Polynomial.X_pow_dvd_iff.mp same_truncation _ order_lt
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero q_ne diff_ne)) zero_coeff

end LocalMultiplication

section Specialization

variable {K : Type*} [Field K]

theorem contact_specializes (values : Fin 5 → Polynomial K) (factor : Polynomial K)
    (m : ℕ) (Q q B : MvPolynomial (Fin 5) K)
    (T_factor : factor ∣ values 0)
    (V₀_factor : factor ∣ values 1)
    (V₁_factor : factor ∣ values 2)
    (row_zero : MvPolynomial.eval₂Hom Polynomial.C values q = 0)
    (contact : ∀ d ∈ (Q - q * B).support, m ≤ d 0 + d 1 + d 2) :
    factor ^ m ∣ MvPolynomial.eval₂Hom Polynomial.C values Q := by
  classical
  have relative_dvd : factor ^ m ∣ MvPolynomial.eval₂Hom Polynomial.C values (Q - q * B) := by
    conv_rhs => rw [MvPolynomial.as_sum (Q - q * B), map_sum]
    apply Finset.dvd_sum
    intro d hd
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have idx₁ : (0 : Fin 4).succ = (1 : Fin 5) := by decide
    have idx₂ : (0 : Fin 3).succ.succ = (2 : Fin 5) := by decide
    have idx₃ : (0 : Fin 2).succ.succ.succ = (3 : Fin 5) := by decide
    have idx₄ : (0 : Fin 1).succ.succ.succ.succ = (4 : Fin 5) := by decide
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, idx₁, idx₂, idx₃, idx₄]
    have local_dvd : factor ^ (d 0 + d 1 + d 2) ∣
        values 0 ^ d 0 * (values 1 ^ d 1 * values 2 ^ d 2) := by
      rw [Nat.add_assoc, pow_add, pow_add]
      exact mul_dvd_mul (pow_dvd_pow_of_dvd T_factor _)
        (mul_dvd_mul (pow_dvd_pow_of_dvd V₀_factor _) (pow_dvd_pow_of_dvd V₁_factor _))
    have h := (pow_dvd_pow factor (contact d hd)).trans local_dvd
    have h := dvd_mul_of_dvd_left h
      (values 3 ^ d 3 * values 4 ^ d 4)
    simpa only [mul_assoc] using
      dvd_mul_of_dvd_right h (Polynomial.C ((Q - q * B).coeff d))
  simpa only [map_sub, map_mul, row_zero, zero_mul, sub_zero] using relative_dvd

noncomputable def centerAtNode (x u₀ v₀ u₁ v₁ : K) :
    MvPolynomial (Fin 5) K →ₐ[K] MvPolynomial (Fin 5) K :=
  MvPolynomial.aeval
    ![MvPolynomial.X 0 + MvPolynomial.C x,
      MvPolynomial.X 1 + MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C v₀,
      MvPolynomial.X 2 + MvPolynomial.C u₁ + MvPolynomial.X 4 * MvPolynomial.C v₁,
      MvPolynomial.X 3, MvPolynomial.X 4]

noncomputable def specialize (P₀ P₁ : Polynomial K) (g₀ g₁ : K) :
    MvPolynomial (Fin 5) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, P₀, P₁, Polynomial.C g₀, Polynomial.C g₁]

private noncomputable def localValues (P₀ P₁ : Polynomial K) (g₀ g₁ x u₀ v₀ u₁ v₁ : K) :
    Fin 5 → Polynomial K :=
  ![Polynomial.X - Polynomial.C x,
    P₀ - Polynomial.C (u₀ + g₀ * v₀), P₁ - Polynomial.C (u₁ + g₁ * v₁),
    Polynomial.C g₀, Polynomial.C g₁]

private theorem realize_center (P₀ P₁ : Polynomial K) (g₀ g₁ x u₀ v₀ u₁ v₁ : K)
    (Q : MvPolynomial (Fin 5) K) :
    MvPolynomial.eval₂Hom Polynomial.C (localValues P₀ P₁ g₀ g₁ x u₀ v₀ u₁ v₁)
        (centerAtNode x u₀ v₀ u₁ v₁ Q) = specialize P₀ P₁ g₀ g₁ Q := by
  have realizes :
      (MvPolynomial.aeval (localValues P₀ P₁ g₀ g₁ x u₀ v₀ u₁ v₁)).comp
        (centerAtNode x u₀ v₀ u₁ v₁) = specialize P₀ P₁ g₀ g₁ := by
    ext i
    fin_cases i <;>
      simp [centerAtNode, specialize, localValues] <;> ring
  exact DFunLike.congr_fun realizes Q

theorem shifted_power_dvd_specialization (P₀ P₁ : Polynomial K)
    (g₀ g₁ x u₀ v₀ u₁ v₁ : K) (m : ℕ) (Q q B : MvPolynomial (Fin 5) K)
    (agreement₀ : P₀.eval x = u₀ + g₀ * v₀)
    (agreement₁ : P₁.eval x = u₁ + g₁ * v₁)
    (row_zero : specialize P₀ P₁ g₀ g₁ q = 0)
    (relative_contact : ∀ d ∈
      (centerAtNode x u₀ v₀ u₁ v₁ Q - centerAtNode x u₀ v₀ u₁ v₁ q * B).support,
        m ≤ d 0 + d 1 + d 2) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ specialize P₀ P₁ g₀ g₁ Q := by
  let V := localValues P₀ P₁ g₀ g₁ x u₀ v₀ u₁ v₁
  have V₀_div : Polynomial.X - Polynomial.C x ∣ V 1 := by
    change Polynomial.X - Polynomial.C x ∣ P₀ - Polynomial.C (u₀ + g₀ * v₀)
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, agreement₀]
  have V₁_div : Polynomial.X - Polynomial.C x ∣ V 2 := by
    change Polynomial.X - Polynomial.C x ∣ P₁ - Polynomial.C (u₁ + g₁ * v₁)
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, agreement₁]
  have local_row_zero :
      MvPolynomial.eval₂Hom Polynomial.C V (centerAtNode x u₀ v₀ u₁ v₁ q) = 0 := by
    rw [realize_center, row_zero]
  have root := contact_specializes V (Polynomial.X - Polynomial.C x) m
    (centerAtNode x u₀ v₀ u₁ v₁ Q) (centerAtNode x u₀ v₀ u₁ v₁ q) B
    (show Polynomial.X - Polynomial.C x ∣ V 0 from dvd_refl _) V₀_div V₁_div
    local_row_zero relative_contact
  rwa [realize_center] at root

private theorem specialization_monomial_degree (P₀ P₁ : Polynomial K) (g₀ g₁ : K) (w : ℕ)
    (degree₀ : P₀.natDegree ≤ w) (degree₁ : P₁.natDegree ≤ w)
    (d : Fin 5 →₀ ℕ) (a : K) :
    (specialize P₀ P₁ g₀ g₁ (MvPolynomial.monomial d a)).natDegree ≤
      d 0 + w * (d 1 + d 2) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
  have dC : (specialize P₀ P₁ g₀ g₁ (MvPolynomial.C a)).natDegree ≤ 0 := by
    simp [specialize]
  have dX : ((specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 0)) ^ d 0).natDegree ≤ d 0 := by
    simp [specialize]
  have dY₀ : ((specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 1)) ^ d 1).natDegree ≤ d 1 * w := by
    simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 1) degree₀
  have dY₁ : ((specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 2)) ^ d 2).natDegree ≤ d 2 * w := by
    simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 2) degree₁
  have dZ₀ : ((specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 3)) ^ d 3).natDegree ≤ 0 := by
    rw [show specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 3) = Polynomial.C g₀ by simp [specialize],
      ← Polynomial.C_pow, Polynomial.natDegree_C]
  have dZ₁ : ((specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 4)) ^ d 4).natDegree ≤ 0 := by
    rw [show specialize P₀ P₁ g₀ g₁ (MvPolynomial.X 4) = Polynomial.C g₁ by simp [specialize],
      ← Polynomial.C_pow, Polynomial.natDegree_C]
  have combined := Polynomial.natDegree_mul_le_of_le dC
    (Polynomial.natDegree_mul_le_of_le dX (Polynomial.natDegree_mul_le_of_le dY₀
      (Polynomial.natDegree_mul_le_of_le dY₁ (Polynomial.natDegree_mul_le_of_le dZ₀ dZ₁))))
  simpa [Nat.mul_add, Nat.mul_comm, Nat.add_assoc] using combined

theorem specialization_degree_lt (Q : MvPolynomial (Fin 5) K) (P₀ P₁ : Polynomial K)
    (g₀ g₁ : K) (w D : ℕ) (degree₀ : P₀.natDegree ≤ w) (degree₁ : P₁.natDegree ≤ w)
    (positive : 0 < D)
    (support_bound : ∀ d ∈ Q.support, d 0 + w * (d 1 + d 2) < D) :
    (specialize P₀ P₁ g₀ g₁ Q).natDegree < D := by
  classical
  have term_bound : ∀ d ∈ Q.support,
      (specialize P₀ P₁ g₀ g₁ (MvPolynomial.monomial d (Q.coeff d))).natDegree ≤ D - 1 := by
    intro d in_support
    have h := support_bound d in_support
    have := specialization_monomial_degree P₀ P₁ g₀ g₁ w degree₀ degree₁ d (Q.coeff d)
    omega
  rw [MvPolynomial.as_sum Q, map_sum]
  exact (Polynomial.natDegree_sum_le_of_forall_le Q.support _ term_bound).trans_lt (by omega)

theorem specialization_zero_of_relative_contacts {I : Type*}
    (nodes : I ↪ K) (good : Finset I) (received₀ slope₀ received₁ slope₁ : I → K)
    (P₀ P₁ : Polynomial K) (g₀ g₁ : K) (m w D : ℕ)
    (Q q : MvPolynomial (Fin 5) K)
    (degree₀ : P₀.natDegree ≤ w) (degree₁ : P₁.natDegree ≤ w)
    (positive : 0 < D) (enough_nodes : D ≤ m * good.card)
    (support_bound : ∀ d ∈ Q.support, d 0 + w * (d 1 + d 2) < D)
    (row_zero : specialize P₀ P₁ g₀ g₁ q = 0)
    (agreement₀ : ∀ i ∈ good, P₀.eval (nodes i) = received₀ i + g₀ * slope₀ i)
    (agreement₁ : ∀ i ∈ good, P₁.eval (nodes i) = received₁ i + g₁ * slope₁ i)
    (relative_contacts : ∀ i ∈ good, ∃ B : MvPolynomial (Fin 5) K,
      ∀ d ∈ (centerAtNode (nodes i) (received₀ i) (slope₀ i) (received₁ i) (slope₁ i) Q -
        centerAtNode (nodes i) (received₀ i) (slope₀ i) (received₁ i) (slope₁ i) q * B).support,
          m ≤ d 0 + d 1 + d 2) :
    specialize P₀ P₁ g₀ g₁ Q = 0 := by
  classical
  let factors := fun i : I => (Polynomial.X - Polynomial.C (nodes i)) ^ m
  have divides : (∏ i ∈ good, factors i) ∣ specialize P₀ P₁ g₀ g₁ Q := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ different
      exact (Polynomial.pairwise_coprime_X_sub_C nodes.injective different).pow
    · intro i in_good
      obtain ⟨B, contact⟩ := relative_contacts i in_good
      exact shifted_power_dvd_specialization P₀ P₁ g₀ g₁ (nodes i)
        (received₀ i) (slope₀ i) (received₁ i) (slope₁ i) m Q q B
        (agreement₀ i in_good) (agreement₁ i in_good) row_zero contact
  have factors_degree : (∏ i ∈ good, factors i).natDegree = m * good.card := by
    rw [Polynomial.natDegree_prod_of_monic good factors
      (fun i _ => (Polynomial.monic_X_sub_C (nodes i)).pow m)]
    simp [factors, Polynomial.natDegree_pow, Nat.mul_comm]
  by_contra nonzero
  have lower := Polynomial.natDegree_le_of_dvd divides nonzero
  have upper := specialization_degree_lt Q P₀ P₁ g₀ g₁ w D degree₀ degree₁ positive support_bound
  omega

end Specialization

end ProximityPrize.SubmissionLower.Koala6831Quotient

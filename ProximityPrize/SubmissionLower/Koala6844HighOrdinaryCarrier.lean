import ProximityPrize.SubmissionLower.Koala6831OrdinaryCarrier
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryInterpolation

namespace ProximityPrize.SubmissionLower.Koala6844HighOrdinary

open MvPolynomial Koala6844HighOrdinaryQuotient
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K]

export Koala6831Ordinary (Carrier carrierCoordinates carrierCoordinates_injective retainCarrier retainCarrier_injective comparisonRow carrierFromInterpolant row_dvd_carrier_difference carrier_nonzero carrier_vanishes carrier_support_caps)


theorem exists_ordinary_carrier_6844 {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (β a b : Carrier K) (b_ne : b ≠ 0)
    (idx : Fin 9) (δ : ℕ) (large : 11500 ≤ δ) (small : δ ≤ 31614)
    (β_value : weightDegree valueWeights (retainCarrier β) = 0)
    (a_value : weightDegree valueWeights (retainCarrier a) = 0)
    (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (β_total : weightDegree totalWeights (retainCarrier β) ≤ idx.val + 2)
    (a_total : weightDegree totalWeights (retainCarrier a) ≤ idx.val + 1)
    (b_total : weightDegree totalWeights (retainCarrier b) ≤ idx.val + 1)
    (q_prime : Prime (comparisonRow β a b))
    (q_code : weightDegree (codeWeights 131071) (comparisonRow β a b) = 131071 + δ)
    (q_value : weightDegree valueWeights (comparisonRow β a b) = 1)
    (q_total : weightDegree totalWeights (comparisonRow β a b) = idx.val + 2)
    (q_order : ∀ i, (weightLift germWeights
      (centerAtNode (nodes i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) (comparisonRow β a b))).natTrailingDegree = 1)
    (P₀ P₁ : Γ → Polynomial K) (g₀ g₁ : Γ → K) (agreement : Γ → Finset I)
    (degree₀ : ∀ g, (P₀ g).natDegree ≤ 131071) (degree₁ : ∀ g, (P₁ g).natDegree ≤ 131071)
    (number_agreeing : ∀ g, 180957 ≤ (agreement g).card)
    (agree₀ : ∀ g i, i ∈ agreement g → (P₀ g).eval (nodes i) = u₀ i + g₀ g * v₀ i)
    (agree₁ : ∀ g i, i ∈ agreement g → (P₁ g).eval (nodes i) = u₁ i + g₁ g * v₁ i)
    (q_zero : ∀ g, specialize (P₀ g) (P₁ g) (g₀ g) (g₁ g) (comparisonRow β a b) = 0) :
    let (_, y, L) := ordinaryProfiles idx
    ∃ G : Carrier K, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ L + (idx.val + 1) * y) ∧
      ∀ g, MvPolynomial.aeval ![Polynomial.X, P₀ g, Polynomial.C (g₀ g), Polynomial.C (g₁ g)] G = 0 := by
  have interpolant := exists_ordinary_interpolant_6844 (fun i => nodes i) u₀ v₀ u₁ v₁
    (comparisonRow β a b) q_prime.ne_zero idx δ large small node_count q_code q_value q_total q_order
  cases profile : ordinaryProfiles idx with
  | mk m data =>
      obtain ⟨y, L⟩ := data
      simp only [profile] at interpolant ⊢
      obtain ⟨Q, Q_box, proper, contacts⟩ := interpolant
      have support := (MvPolynomial.mem_restrictSupport_iff K).mp Q_box
      have Q_cap : ∀ d ∈ Q.support, d 1 + d 2 ≤ y ∧ d 1 + d 2 + d 3 + d 4 ≤ L :=
        fun d hd => (support hd).2
      have Q_y : ∀ d ∈ Q.support, d 2 ≤ y := by
        intro d hd
        have bound := (Q_cap d hd).1
        omega
      have positive : 0 < m * 180957 := by
        have Q_ne : Q ≠ 0 := fun hz => proper (by rw [hz]; exact dvd_zero _)
        obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr Q_ne
        exact Nat.zero_lt_of_lt (support hd).1
      refine ⟨carrierFromInterpolant β a b y Q,
        carrier_nonzero β a b y Q b_ne b_value q_prime q_value proper Q_y, ?_, ?_⟩
      · intro d hd
        exact carrier_support_caps β a b y L (idx.val + 2) Q (by omega)
          β_value a_value b_value β_total a_total b_total Q_cap d hd
      · intro g
        apply carrier_vanishes β a b y Q Q_y (P₀ g) (P₁ g) (g₀ g) (g₁ g) (q_zero g)
        apply specialization_zero_of_relative_contacts nodes (agreement g) u₀ v₀ u₁ v₁
          (P₀ g) (P₁ g) (g₀ g) (g₁ g) m 131071 (m * 180957) Q (comparisonRow β a b)
          (degree₀ g) (degree₁ g) positive (Nat.mul_le_mul_left m (number_agreeing g))
          (fun d hd => (support hd).1) (q_zero g) (agree₀ g) (agree₁ g) (fun i _ => contacts i)

end

end ProximityPrize.SubmissionLower.Koala6844HighOrdinary

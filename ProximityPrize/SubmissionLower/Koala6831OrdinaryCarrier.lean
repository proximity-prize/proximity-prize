import ProximityPrize.SubmissionLower.Koala6831OrdinaryInterpolation
import Mathlib.Algebra.Ring.GeomSum

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open MvPolynomial Koala6831Quotient
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

abbrev Carrier (K : Type*) [CommSemiring K] := MvPolynomial (Fin 4) K

def carrierCoordinates : Fin 4 → Fin 5 := ![0, 1, 3, 4]

theorem carrierCoordinates_injective : Function.Injective carrierCoordinates := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [carrierCoordinates] at h)

def retainCarrier : Carrier K →ₐ[K] Poly K := MvPolynomial.rename carrierCoordinates

theorem retainCarrier_injective : Function.Injective (retainCarrier (K := K)) :=
  MvPolynomial.rename_injective _ carrierCoordinates_injective

def comparisonRow (β a b : Carrier K) : Poly K :=
  retainCarrier β + retainCarrier a * X 1 + retainCarrier b * X 2

private def keptMonomial (d : Fin 5 →₀ ℕ) (a : K) : Carrier K :=
  C a * X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 3 * X 3 ^ d 4

private theorem keptMonomial_lift (d : Fin 5 →₀ ℕ) (a : K) :
    retainCarrier (keptMonomial d a) =
      C a * X 0 ^ d 0 * X 1 ^ d 1 * X 3 ^ d 3 * X 4 ^ d 4 := by
  simp [retainCarrier, keptMonomial, carrierCoordinates]

private theorem keptMonomial_mul (d : Fin 5 →₀ ℕ) (a : K) :
    MvPolynomial.monomial d a = retainCarrier (keptMonomial d a) * X 2 ^ d 2 := by
  rw [keptMonomial_lift, MvPolynomial.monomial_eq, Finsupp.prod_pow]
  have idx₁ : (0 : Fin 4).succ = (1 : Fin 5) := by decide
  have idx₂ : (0 : Fin 3).succ.succ = (2 : Fin 5) := by decide
  have idx₃ : (0 : Fin 2).succ.succ.succ = (3 : Fin 5) := by decide
  have idx₄ : (0 : Fin 1).succ.succ.succ.succ = (4 : Fin 5) := by decide
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, idx₁, idx₂, idx₃, idx₄]
  ring

private def eliminatedTerm (β a b : Carrier K) (y : ℕ) (Q : Poly K) (d : Fin 5 →₀ ℕ) : Carrier K :=
  keptMonomial d (Q.coeff d) * b ^ (y - d 2) * (-(β + a * X 1)) ^ d 2

def carrierFromInterpolant (β a b : Carrier K) (y : ℕ) (Q : Poly K) : Carrier K :=
  ∑ d ∈ Q.support, eliminatedTerm β a b y Q d

private theorem row_dvd_monomial_difference (β a b : Carrier K) (y : ℕ) (Q : Poly K)
    (d : Fin 5 →₀ ℕ) (cap : d 2 ≤ y) :
    comparisonRow β a b ∣ (retainCarrier b) ^ y * MvPolynomial.monomial d (Q.coeff d) -
      retainCarrier (eliminatedTerm β a b y Q d) := by
  let numerator := retainCarrier β + retainCarrier a * X 1
  have difference : comparisonRow β a b ∣ (retainCarrier b * X 2) ^ d 2 - (-numerator) ^ d 2 := by
    have row_eq : comparisonRow β a b = retainCarrier b * X 2 - (-numerator) := by
      simp only [comparisonRow, numerator, sub_neg_eq_add]
      rw [add_comm]
    rw [row_eq]
    exact sub_dvd_pow_sub_pow (retainCarrier b * X 2) (-numerator) (d 2)
  have multiplied := dvd_mul_of_dvd_right difference
    (retainCarrier (keptMonomial d (Q.coeff d)) * (retainCarrier b) ^ (y - d 2))
  have power_split : (retainCarrier b) ^ y = (retainCarrier b) ^ (y - d 2) * (retainCarrier b) ^ d 2 := by
    rw [← pow_add, Nat.sub_add_cancel cap]
  rw [power_split, keptMonomial_mul]
  simp only [eliminatedTerm, map_add, map_mul, map_pow, map_neg]
  have Y_one : retainCarrier (X 1 : Carrier K) = X 1 := by simp [retainCarrier, carrierCoordinates]
  rw [Y_one]
  convert multiplied using 1
  rw [mul_pow]
  change _ = _ * (_ - (-(retainCarrier β + retainCarrier a * X 1)) ^ d 2)
  ring

theorem row_dvd_carrier_difference (β a b : Carrier K) (y : ℕ) (Q : Poly K)
    (cap : ∀ d ∈ Q.support, d 2 ≤ y) :
    comparisonRow β a b ∣ (retainCarrier b) ^ y * Q - retainCarrier (carrierFromInterpolant β a b y Q) := by
  have expanded : (retainCarrier b) ^ y * Q =
      ∑ d ∈ Q.support, (retainCarrier b) ^ y * MvPolynomial.monomial d (Q.coeff d) := by
    conv_lhs => rw [MvPolynomial.as_sum Q, Finset.mul_sum]
  rw [expanded, carrierFromInterpolant, map_sum, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun d hd => row_dvd_monomial_difference β a b y Q d (cap d hd)

theorem carrier_nonzero (β a b : Carrier K) (y : ℕ) (Q : Poly K)
    (b_ne : b ≠ 0) (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (row_prime : Prime (comparisonRow β a b))
    (row_value : weightDegree valueWeights (comparisonRow β a b) = 1)
    (proper : ¬ comparisonRow β a b ∣ Q) (cap : ∀ d ∈ Q.support, d 2 ≤ y) :
    carrierFromInterpolant β a b y Q ≠ 0 := by
  intro zero
  have divides := row_dvd_carrier_difference β a b y Q cap
  simp only [zero, map_zero, sub_zero] at divides
  rcases row_prime.dvd_mul.mp divides with power | hQ
  · have hdiv := row_prime.dvd_of_dvd_pow power
    obtain ⟨T, hT⟩ := hdiv
    have lifted_nonzero : retainCarrier b ≠ 0 := by
      intro zero
      exact b_ne (retainCarrier_injective (by simpa only [map_zero] using zero))
    have T_nonzero : T ≠ 0 := by
      intro zero
      exact lifted_nonzero (by simp [hT, zero])
    have degree := weight_mul_eq valueWeights row_prime.ne_zero T_nonzero
    rw [← hT, b_value, row_value] at degree
    omega
  · exact proper hQ

private def specializeCarrier (P : Polynomial K) (g₀ g₁ : K) : Carrier K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, P, Polynomial.C g₀, Polynomial.C g₁]

private theorem specialize_retain (P R : Polynomial K) (g₀ g₁ : K) (F : Carrier K) :
    specialize P R g₀ g₁ (retainCarrier F) = specializeCarrier P g₀ g₁ F := by
  have h : (specialize P R g₀ g₁).comp retainCarrier = specializeCarrier P g₀ g₁ := by
    ext i
    fin_cases i <;> simp [retainCarrier, carrierCoordinates, specialize, specializeCarrier]
  exact DFunLike.congr_fun h F

theorem carrier_vanishes (β a b : Carrier K) (y : ℕ) (Q : Poly K)
    (cap : ∀ d ∈ Q.support, d 2 ≤ y) (P R : Polynomial K) (g₀ g₁ : K)
    (row_zero : specialize P R g₀ g₁ (comparisonRow β a b) = 0)
    (Q_zero : specialize P R g₀ g₁ Q = 0) :
    MvPolynomial.aeval ![Polynomial.X, P, Polynomial.C g₀, Polynomial.C g₁]
      (carrierFromInterpolant β a b y Q) = 0 := by
  obtain ⟨H, hH⟩ := row_dvd_carrier_difference β a b y Q cap
  have h := congrArg (specialize P R g₀ g₁) hH
  simpa only [map_sub, map_mul, Q_zero, row_zero, mul_zero, zero_mul,
    zero_sub, neg_eq_zero, specialize_retain, specializeCarrier] using h

private theorem weight_neg_eq (w : Fin 5 → ℕ) (P : Poly K) :
    weightDegree w (-P) = weightDegree w P := by
  simp only [← weightLift_natDegree, map_neg, Polynomial.natDegree_neg]

private theorem weight_pow_le (w : Fin 5 → ℕ) (P : Poly K) (n cap : ℕ)
    (hcap : weightDegree w P ≤ cap) : weightDegree w (P ^ n) ≤ n * cap := by
  rw [← weightLift_natDegree, map_pow]
  exact Polynomial.natDegree_pow_le_of_le n (by simpa only [weightLift_natDegree] using hcap)

private theorem weight_sum_le {ι : Type*} (w : Fin 5 → ℕ) (S : Finset ι)
    (f : ι → Poly K) (cap : ℕ) (hcap : ∀ d ∈ S, weightDegree w (f d) ≤ cap) :
    weightDegree w (∑ d ∈ S, f d) ≤ cap := by
  rw [← weightLift_natDegree, map_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le S _ (fun d hd => by
    rw [weightLift_natDegree]
    exact hcap d hd)

private theorem keptMonomial_weight_le (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) (a : K) :
    weightDegree w (retainCarrier (keptMonomial d a)) ≤ d 0 * w 0 + d 1 * w 1 + d 3 * w 3 + d 4 * w 4 := by
  rw [keptMonomial_lift]
  have single (i : Fin 5) : weightDegree w ((X i : Poly K) ^ d i) ≤ d i * w i :=
    weight_pow_le w (X i) (d i) (w i) (weight_X w i).le
  have first := (weight_mul_le w (C a) (X 0 ^ d 0)).trans
    (Nat.add_le_add (weight_C w a).le (single 0))
  have second := (weight_mul_le w _ (X 1 ^ d 1)).trans (Nat.add_le_add first (single 1))
  have third := (weight_mul_le w _ (X 3 ^ d 3)).trans (Nat.add_le_add second (single 3))
  simpa only [zero_add] using
    (weight_mul_le w _ (X 4 ^ d 4)).trans (Nat.add_le_add third (single 4))

private theorem liftedTerm_value_le (β a b : Carrier K) (y : ℕ) (Q : Poly K)
    (β_value : weightDegree valueWeights (retainCarrier β) = 0)
    (a_value : weightDegree valueWeights (retainCarrier a) = 0)
    (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (d : Fin 5 →₀ ℕ) (h : d 1 + d 2 ≤ y) :
    weightDegree valueWeights (retainCarrier (eliminatedTerm β a b y Q d)) ≤ y := by
  let w := valueWeights
  have Y_one : retainCarrier (X 1 : Carrier K) = X 1 := by simp [retainCarrier, carrierCoordinates]
  have first : weightDegree valueWeights (retainCarrier (keptMonomial d (Q.coeff d))) ≤ d 1 := by
    simpa [valueWeights] using keptMonomial_weight_le valueWeights d (Q.coeff d)
  have second : weightDegree valueWeights ((retainCarrier b) ^ (y - d 2)) ≤ 0 := by
    simpa only [Nat.mul_zero] using weight_pow_le valueWeights (retainCarrier b) (y-d 2) 0 b_value.le
  have numerator : weightDegree valueWeights (-(retainCarrier β + retainCarrier a * X 1)) ≤ 1 := by
    rw [weight_neg_eq]
    apply (weight_add_le _ _ _).trans
    apply max_le
    · rw [β_value]
      decide
    · apply (weight_mul_le _ _ _).trans
      rw [a_value, weight_X, zero_add]
      decide
  have third : weightDegree valueWeights ((-(retainCarrier β + retainCarrier a * X 1)) ^ d 2) ≤ d 2 := by
    simpa only [Nat.mul_one] using weight_pow_le valueWeights _ (d 2) 1 numerator
  simp only [eliminatedTerm, map_mul, map_pow, map_neg, map_add, Y_one]
  exact ((weight_mul_le w _ _).trans (Nat.add_le_add
    ((weight_mul_le w _ _).trans (Nat.add_le_add first second)) third)).trans (by omega)

private theorem liftedTerm_total_le (β a b : Carrier K) (y L c : ℕ) (Q : Poly K)
    (c_pos : 0 < c)
    (β_total : weightDegree totalWeights (retainCarrier β) ≤ c)
    (a_total : weightDegree totalWeights (retainCarrier a) ≤ c - 1)
    (b_total : weightDegree totalWeights (retainCarrier b) ≤ c - 1)
    (d : Fin 5 →₀ ℕ) (hY : d 2 ≤ y) (hL : d 1 + d 2 + d 3 + d 4 ≤ L) :
    weightDegree totalWeights (retainCarrier (eliminatedTerm β a b y Q d)) ≤ L + (c - 1) * y := by
  let w := totalWeights
  have Y_one : retainCarrier (X 1 : Carrier K) = X 1 := by simp [retainCarrier, carrierCoordinates]
  have first : weightDegree totalWeights (retainCarrier (keptMonomial d (Q.coeff d))) ≤ d 1 + d 3 + d 4 := by
    simpa [totalWeights] using keptMonomial_weight_le totalWeights d (Q.coeff d)
  have second := weight_pow_le totalWeights (retainCarrier b) (y - d 2) (c - 1) b_total
  have numerator : weightDegree totalWeights (-(retainCarrier β + retainCarrier a * X 1)) ≤ c := by
    rw [weight_neg_eq]
    apply (weight_add_le _ _ _).trans
    apply max_le β_total
    apply (weight_mul_le _ _ _).trans
    rw [weight_X, show totalWeights 1 = 1 from rfl]
    omega
  have third := weight_pow_le totalWeights _ (d 2) c numerator
  have power_sum : (y - d 2) * (c - 1) + d 2 * c = (c - 1) * y + d 2 := by
    have factor : d 2 * c = d 2 * (c - 1) + d 2 := by
      calc
        d 2 * c = d 2 * ((c - 1) + 1) := by
          congr 1
          omega
        _ = _ := by simp [Nat.mul_add]
    rw [factor, ← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hY, Nat.mul_comm y]
  simp only [eliminatedTerm, map_mul, map_pow, map_neg, map_add, Y_one]
  apply ((weight_mul_le w _ _).trans (Nat.add_le_add
    ((weight_mul_le w _ _).trans (Nat.add_le_add first second)) third)).trans
  omega

private theorem lifted_exponent_coordinate (d : Fin 4 →₀ ℕ) (i : Fin 4) :
    (Finsupp.mapDomain carrierCoordinates d) (carrierCoordinates i) = d i :=
  Finsupp.mapDomain_apply_of_injective carrierCoordinates_injective d i

theorem carrier_support_caps (β a b : Carrier K) (y L c : ℕ) (Q : Poly K)
    (c_pos : 0 < c)
    (β_value : weightDegree valueWeights (retainCarrier β) = 0)
    (a_value : weightDegree valueWeights (retainCarrier a) = 0)
    (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (β_total : weightDegree totalWeights (retainCarrier β) ≤ c)
    (a_total : weightDegree totalWeights (retainCarrier a) ≤ c - 1)
    (b_total : weightDegree totalWeights (retainCarrier b) ≤ c - 1)
    (Q_cap : ∀ d ∈ Q.support, d 1 + d 2 ≤ y ∧ d 1 + d 2 + d 3 + d 4 ≤ L) :
    ∀ d ∈ (carrierFromInterpolant β a b y Q).support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ L + (c - 1) * y := by
  let G := carrierFromInterpolant β a b y Q
  have y_bound : weightDegree valueWeights (retainCarrier G) ≤ y := by
    rw [show G = carrierFromInterpolant β a b y Q from rfl, carrierFromInterpolant, map_sum]
    exact weight_sum_le valueWeights _ _ _ (fun d hd => liftedTerm_value_le β a b y Q
      β_value a_value b_value d (Q_cap d hd).1)
  have t_bound : weightDegree totalWeights (retainCarrier G) ≤ L + (c - 1) * y := by
    rw [show G = carrierFromInterpolant β a b y Q from rfl, carrierFromInterpolant, map_sum]
    exact weight_sum_le totalWeights _ _ _ (fun d hd => liftedTerm_total_le β a b y L c Q
      c_pos β_total a_total b_total d (by have := (Q_cap d hd).1; omega) (Q_cap d hd).2)
  intro d hd
  let e := Finsupp.mapDomain carrierCoordinates d
  have in_lift : e ∈ (retainCarrier G).support := by
    rw [retainCarrier, MvPolynomial.support_rename_of_injective carrierCoordinates_injective]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have e1 : e 1 = d 1 := lifted_exponent_coordinate d 1
  have e3 : e 3 = d 2 := lifted_exponent_coordinate d 2
  have e4 : e 4 = d 3 := lifted_exponent_coordinate d 3
  have v := (le_weightedTotalDegree valueWeights in_lift).trans y_bound
  have t := (le_weightedTotalDegree totalWeights in_lift).trans t_bound
  simp only [value_weight, total_weight, e1, e3, e4] at v t
  omega

theorem exists_ordinary_carrier_6831 {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (β a b : Carrier K) (b_ne : b ≠ 0)
    (idx : Fin 9) (δ : ℕ) (large : 11000 ≤ δ) (small : δ ≤ 31357)
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
    (number_agreeing : ∀ g, 181078 ≤ (agreement g).card)
    (agree₀ : ∀ g i, i ∈ agreement g → (P₀ g).eval (nodes i) = u₀ i + g₀ g * v₀ i)
    (agree₁ : ∀ g i, i ∈ agreement g → (P₁ g).eval (nodes i) = u₁ i + g₁ g * v₁ i)
    (q_zero : ∀ g, specialize (P₀ g) (P₁ g) (g₀ g) (g₁ g) (comparisonRow β a b) = 0) :
    let (_, y, L) := ordinaryProfiles idx
    ∃ G : Carrier K, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ L + (idx.val + 1) * y) ∧
      ∀ g, MvPolynomial.aeval ![Polynomial.X, P₀ g, Polynomial.C (g₀ g), Polynomial.C (g₁ g)] G = 0 := by
  have interpolant := exists_ordinary_interpolant_6831 (fun i => nodes i) u₀ v₀ u₁ v₁
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
      have positive : 0 < m * 181078 := by
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
          (P₀ g) (P₁ g) (g₀ g) (g₁ g) m 131071 (m * 181078) Q (comparisonRow β a b)
          (degree₀ g) (degree₁ g) positive (Nat.mul_le_mul_left m (number_agreeing g))
          (fun d hd => (support hd).1) (q_zero g) (agree₀ g) (agree₁ g) (fun i _ => contacts i)

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryCarrier
import ProximityPrize.SubmissionLower.Koala6844HighSeparatedInterpolation


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open MvPolynomial Koala6844HighOrdinary Koala6844HighOrdinaryQuotient
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private theorem weight_pow_le (w : Fin 5 → ℕ) (P : Poly K) (n cap : ℕ)
    (hcap : weightDegree w P ≤ cap) : weightDegree w (P ^ n) ≤ n * cap := by
  rw [← weightLift_natDegree, map_pow]
  exact Polynomial.natDegree_pow_le_of_le n (by simpa only [weightLift_natDegree] using hcap)

private theorem weight_sum_le {ι : Type*} (w : Fin 5 → ℕ) (S : Finset ι)
    (f : ι → Poly K) (cap : ℕ) (hcap : ∀ i ∈ S, weightDegree w (f i) ≤ cap) :
    weightDegree w (∑ i ∈ S, f i) ≤ cap := by
  rw [← weightLift_natDegree, map_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le S _ (fun i hi => by
    rw [weightLift_natDegree]
    exact hcap i hi)

private def kept (d : Fin 5 →₀ ℕ) (a : K) : Carrier K :=
  C a * X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 3 * X 3 ^ d 4

private theorem kept_weight_le (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) (a : K) :
    weightDegree w (retainCarrier (kept d a)) ≤
      d 0 * w 0 + d 1 * w 1 + d 3 * w 3 + d 4 * w 4 := by
  have lift : retainCarrier (kept d a) =
      C a * X 0 ^ d 0 * X 1 ^ d 1 * X 3 ^ d 3 * X 4 ^ d 4 := by
    simp [retainCarrier, kept, carrierCoordinates]
  rw [lift]
  have single (i : Fin 5) : weightDegree w ((X i : Poly K) ^ d i) ≤ d i * w i :=
    weight_pow_le w (X i) (d i) (w i) (weight_X w i).le
  have h₀ := (weight_mul_le w ((C a : Poly K)) (X 0 ^ d 0)).trans
    (Nat.add_le_add (weight_C w a).le (single 0))
  have h₁ := (weight_mul_le w _ (X 1 ^ d 1)).trans (Nat.add_le_add h₀ (single 1))
  have h₃ := (weight_mul_le w _ (X 3 ^ d 3)).trans (Nat.add_le_add h₁ (single 3))
  simpa only [zero_add] using
    (weight_mul_le w _ (X 4 ^ d 4)).trans (Nat.add_le_add h₃ (single 4))

private theorem cleared_weight_le (w : Fin 5 → ℕ) (β a b : Carrier K) (Q : Poly K) (s B N cap : ℕ)
    (hb : weightDegree w (retainCarrier b) ≤ B)
    (hn : weightDegree w (-(retainCarrier β + retainCarrier a * X 1)) ≤ N)
    (support : ∀ d ∈ Q.support,
      d 0 * w 0 + d 1 * w 1 + d 3 * w 3 + d 4 * w 4 + (s - d 2) * B + d 2 * N ≤ cap) :
    weightDegree w (retainCarrier (carrierFromInterpolant β a b s Q)) ≤ cap := by
  change weightDegree w (retainCarrier (∑ d ∈ Q.support,
    kept d (Q.coeff d) * b ^ (s - d 2) * (-(β + a * X 1)) ^ d 2)) ≤ cap
  have Y_one : retainCarrier (X 1 : Carrier K) = X 1 := by simp [retainCarrier, carrierCoordinates]
  simp only [map_sum, map_mul, map_pow, map_neg, map_add, Y_one]
  apply weight_sum_le
  intro d hd
  have ht := kept_weight_le w d (Q.coeff d)
  have hB := weight_pow_le w (retainCarrier b) (s - d 2) B hb
  have hN := weight_pow_le w _ (d 2) N hn
  exact ((weight_mul_le w _ _).trans
    (Nat.add_le_add ((weight_mul_le w _ _).trans (Nat.add_le_add ht hB)) hN)).trans (support d hd)

private theorem numerator_weight_le (w : Fin 5 → ℕ) (β a : Carrier K) (cap : ℕ)
    (hb : weightDegree w (retainCarrier β) ≤ cap)
    (ha : weightDegree w (retainCarrier a) + w 1 ≤ cap) :
    weightDegree w (-(retainCarrier β + retainCarrier a * X 1)) ≤ cap := by
  have hneg : weightDegree w (-(retainCarrier β + retainCarrier a * X 1)) =
      weightDegree w (retainCarrier β + retainCarrier a * X 1) := by
    simp only [← weightLift_natDegree, map_neg, Polynomial.natDegree_neg]
  rw [hneg]
  apply (weight_add_le _ _ _).trans (max_le hb ?_)
  exact (weight_mul_le _ _ _).trans (by rwa [weight_X])

private theorem lifted_coordinate (d : Fin 4 →₀ ℕ) (i : Fin 4) :
    Finsupp.mapDomain carrierCoordinates d (carrierCoordinates i) = d i :=
  Finsupp.mapDomain_apply_of_injective carrierCoordinates_injective d i


theorem support_caps (β a b : Carrier K) (δ : ℕ) (Q : Poly K)
    (Q_box : Q ∈ separatedBox K (16 * 180961) 131071 22 22 178 162)
    (β_value : weightDegree valueWeights (retainCarrier β) = 0)
    (a_value : weightDegree valueWeights (retainCarrier a) = 0)
    (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (β_left : weightDegree leftWeights (retainCarrier β) ≤ 1)
    (a_left : weightDegree leftWeights (retainCarrier a) = 0)
    (b_left : weightDegree leftWeights (retainCarrier b) ≤ 1)
    (β_right : weightDegree rightWeights (retainCarrier β) ≤ 1)
    (a_right : weightDegree rightWeights (retainCarrier a) ≤ 1)
    (b_right : weightDegree rightWeights (retainCarrier b) = 0)
    (β_code : weightDegree (codeWeights 131071) (retainCarrier β) ≤ 131071 + δ)
    (a_code : weightDegree (codeWeights 131071) (retainCarrier a) ≤ δ)
    (b_code : weightDegree (codeWeights 131071) (retainCarrier b) ≤ δ) :
    ∀ d ∈ (carrierFromInterpolant β a b 22 Q).support,
      d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧ d 0 + 131071 * d 1 ≤ 16 * 180961 - 1 + 22 * δ := by
  let G := carrierFromInterpolant β a b 22 Q
  have supp := (MvPolynomial.mem_restrictSupport_iff K).mp Q_box
  have hy : weightDegree valueWeights (retainCarrier G) ≤ 22 := by
    apply cleared_weight_le valueWeights β a b Q 22 0 1 22 b_value.le
      (numerator_weight_le _ β a 1 (by simp [β_value]) (by rw [a_value]; decide))
    intro d hd
    simpa [valueWeights] using (supp hd).2.1
  have ht : weightDegree leftWeights (retainCarrier G) ≤ 200 := by
    apply cleared_weight_le leftWeights β a b Q 22 1 1 200 b_left
      (numerator_weight_le _ β a 1 β_left (by rw [a_left]; decide))
    intro d hd
    have hd₂ := (supp hd).2.2.1
    have hd₀ := (supp hd).2.2.2.1
    change d 2 ≤ 22 at hd₂
    change d 1 + d 3 ≤ 178 at hd₀
    simp [leftWeights]
    omega
  have hz : weightDegree rightWeights (retainCarrier G) ≤ 162 := by
    apply cleared_weight_le rightWeights β a b Q 22 0 1 162 b_right.le
      (numerator_weight_le _ β a 1 β_right (by simpa [rightWeights] using a_right))
    intro d hd
    have hd₁ := (supp hd).2.2.2.2
    simpa [rightWeights, Nat.add_comm] using hd₁
  have hcode : weightDegree (codeWeights 131071) (retainCarrier G) ≤ 16 * 180961 - 1 + 22 * δ := by
    apply cleared_weight_le (codeWeights 131071) β a b Q 22 δ (131071 + δ)
      (16 * 180961 - 1 + 22 * δ) b_code
      (numerator_weight_le _ β a _ β_code (by
        change weightDegree (codeWeights 131071) (retainCarrier a) + 131071 ≤ 131071 + δ
        omega))
    intro d hd
    have hds := (supp hd).2.2.1
    have hdc := (supp hd).1
    change d 2 ≤ 22 at hds
    change d 0 + 131071 * (d 1 + d 2) < 16 * 180961 at hdc
    have hsplit : (22 - d 2) * δ + d 2 * δ = 22 * δ := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hds]
    simp [codeWeights, Nat.mul_add] at *
    omega
  intro d hd
  let e := Finsupp.mapDomain carrierCoordinates d
  have hlift : e ∈ (retainCarrier G).support := by
    rw [retainCarrier, MvPolynomial.support_rename_of_injective carrierCoordinates_injective]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have e₀ : e 0 = d 0 := lifted_coordinate d 0
  have e₁ : e 1 = d 1 := lifted_coordinate d 1
  have e₃ : e 3 = d 2 := lifted_coordinate d 2
  have e₄ : e 4 = d 3 := lifted_coordinate d 3
  have e₂ : e 2 = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [carrierCoordinates] at hj
  have byY := (le_weightedTotalDegree valueWeights hlift).trans hy
  have byT := (le_weightedTotalDegree leftWeights hlift).trans ht
  have byZ := (le_weightedTotalDegree rightWeights hlift).trans hz
  have byX := (le_weightedTotalDegree (codeWeights 131071) hlift).trans hcode
  simpa only [code_weight, value_weight, left_weight, right_weight, e₀, e₁, e₂, e₃, e₄, add_zero,
    zero_add] using And.intro byY (And.intro byT (And.intro byZ byX))


theorem exists_long_carrier {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (β a b : Carrier K) (b_ne : b ≠ 0) (δ : ℕ) (large : 9800 ≤ δ) (small : δ ≤ 31606)
    (β_value : weightDegree valueWeights (retainCarrier β) = 0)
    (a_value : weightDegree valueWeights (retainCarrier a) = 0)
    (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (β_left : weightDegree leftWeights (retainCarrier β) ≤ 1)
    (a_left : weightDegree leftWeights (retainCarrier a) = 0)
    (b_left : weightDegree leftWeights (retainCarrier b) ≤ 1)
    (β_right : weightDegree rightWeights (retainCarrier β) ≤ 1)
    (a_right : weightDegree rightWeights (retainCarrier a) ≤ 1)
    (b_right : weightDegree rightWeights (retainCarrier b) = 0)
    (β_code : weightDegree (codeWeights 131071) (retainCarrier β) ≤ 131071 + δ)
    (a_code : weightDegree (codeWeights 131071) (retainCarrier a) ≤ δ)
    (b_code : weightDegree (codeWeights 131071) (retainCarrier b) ≤ δ)
    (q_prime : Prime (comparisonRow β a b))
    (q_code : weightDegree (codeWeights 131071) (comparisonRow β a b) = 131071 + δ)
    (q_value : weightDegree valueWeights (comparisonRow β a b) = 1)
    (q_second : weightDegree secondWeights (comparisonRow β a b) = 1)
    (q_left : weightDegree leftWeights (comparisonRow β a b) = 1)
    (q_right : weightDegree rightWeights (comparisonRow β a b) = 1)
    (q_order : ∀ i, (weightLift germWeights
      (centerAtNode (nodes i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) (comparisonRow β a b))).natTrailingDegree = 1)
    (P₀ P₁ : Γ → Polynomial K) (g₀ g₁ : Γ → K) (agreement : Γ → Finset I)
    (degree₀ : ∀ g, (P₀ g).natDegree ≤ 131071) (degree₁ : ∀ g, (P₁ g).natDegree ≤ 131071)
    (number_agreeing : ∀ g, 180961 ≤ (agreement g).card)
    (agree₀ : ∀ g i, i ∈ agreement g → (P₀ g).eval (nodes i) = u₀ i + g₀ g * v₀ i)
    (agree₁ : ∀ g i, i ∈ agreement g → (P₁ g).eval (nodes i) = u₁ i + g₁ g * v₁ i)
    (q_zero : ∀ g, specialize (P₀ g) (P₁ g) (g₀ g) (g₁ g) (comparisonRow β a b) = 0) :
    ∃ G : Carrier K, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧
        d 0 + 131071 * d 1 ≤ 16 * 180961 - 1 + 22 * δ) ∧
      ∀ g, MvPolynomial.aeval ![Polynomial.X, P₀ g, Polynomial.C (g₀ g), Polynomial.C (g₁ g)] G = 0 := by
  obtain ⟨Q, hQ, hproper, hcontact⟩ := exists_long_interpolant (fun i => nodes i) u₀ v₀ u₁ v₁
    (comparisonRow β a b) q_prime.ne_zero δ large small node_count q_code q_value q_second
    q_left q_right q_order
  have supp := (MvPolynomial.mem_restrictSupport_iff K).mp hQ
  have cap : ∀ d ∈ Q.support, d 2 ≤ 22 := fun d hd => (supp hd).2.2.1
  refine ⟨carrierFromInterpolant β a b 22 Q,
    carrier_nonzero β a b 22 Q b_ne b_value q_prime q_value hproper cap,
    support_caps β a b δ Q hQ β_value a_value b_value β_left a_left b_left
      β_right a_right b_right β_code a_code b_code, ?_⟩
  intro g
  apply carrier_vanishes β a b 22 Q cap (P₀ g) (P₁ g) (g₀ g) (g₁ g) (q_zero g)
  exact specialization_zero_of_relative_contacts nodes (agreement g) u₀ v₀ u₁ v₁
    (P₀ g) (P₁ g) (g₀ g) (g₁ g) 16 131071 (16 * 180961) Q (comparisonRow β a b)
    (degree₀ g) (degree₁ g) (by decide) (Nat.mul_le_mul_left 16 (number_agreeing g))
    (fun d hd => (supp hd).1) (q_zero g) (agree₀ g) (agree₁ g) (fun i _ => hcontact i)

end

end ProximityPrize.SubmissionLower.Koala6844HighSeparated

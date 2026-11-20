import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryCarrier
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryGoodNode
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryPrimitiveLiftDegrees
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryPrimitivePrime

namespace ProximityPrize.SubmissionLower.Koala6844HighOrdinary

open Koala6844Comparison Koala6844HighOrdinaryQuotient MvPolynomial

variable {K : Type*} [Field K]

theorem exists_ordinary_carrier_of_primitive {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (q : SymbolicRow (SeedRing K)) (hprim : IsPrimitiveRow q)
    (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (hlarge : 11500 ≤ primitiveExcess 131071 q) (hsmall : primitiveExcess 131071 q ≤ 31608)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 10)
    (hgood : ∀ i, q.atNode (MvPolynomial.C (nodes i))
      (MvPolynomial.C (u₀ i) + MvPolynomial.X 0 * MvPolynomial.C (v₀ i))
      (MvPolynomial.C (u₁ i) + MvPolynomial.X 1 * MvPolynomial.C (v₁ i)) = 0)
    (σ : K →+* K) (p : ℕ) (P : K → Polynomial K) (seed : Γ → K)
    (agreement : Γ → Finset I) (hdegree : ∀ g, (P (seed g)).natDegree ≤ 131071)
    (hsize : ∀ g, 180960 ≤ (agreement g).card)
    (h₀ : ∀ g i, i ∈ agreement g → (P (seed g)).eval (nodes i) = u₀ i + seed g * v₀ i)
    (h₁ : ∀ g i, i ∈ agreement g →
      ((P (seed g)).map σ).eval (nodes i) = u₁ i + (seed g) ^ p * v₁ i)
    (hzero : ∀ g, primitiveSelected σ p q P (seed g) = 0) :
    ∃ idx : Fin 9, idx.val + 2 = weightDegree totalWeights (primitiveRowLift q) ∧
      let (_, y, L) := ordinaryProfiles idx
      ∃ G : Carrier K, G ≠ 0 ∧
        (∀ d ∈ G.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ L + (idx.val + 1) * y) ∧
        ∀ g, MvPolynomial.aeval
          ![Polynomial.X, P (seed g), Polynomial.C (seed g), Polynomial.C ((seed g) ^ p)] G = 0 := by
  let c := weightDegree totalWeights (primitiveRowLift q)
  have hc : 2 ≤ c ∧ c ≤ 10 := ⟨hc₂, hc₁₀⟩
  let idx : Fin 9 := ⟨c - 2, by omega⟩
  have hidx : idx.val + 2 = c := by dsimp [idx]; omega
  have hcap : c - 1 ≤ idx.val + 1 := by omega
  obtain ⟨hβ, ha, hb⟩ := primitiveRowLift_total_weight_caps q hf hs
  refine ⟨idx, hidx, ?_⟩
  apply exists_ordinary_carrier_6844 nodes u₀ v₀ u₁ v₁ node_count
    (carrierOfSeedCoefficients q.beta) (carrierOfSeedCoefficients q.first)
    (carrierOfSeedCoefficients q.second) (carrierOfSeedCoefficients_ne_zero hs)
    idx (primitiveExcess 131071 q) hlarge hsmall
    (liftedCoefficient_value_weight q.beta) (liftedCoefficient_value_weight q.first)
    (liftedCoefficient_value_weight q.second) (hβ.trans_eq hidx.symm) (ha.trans hcap) (hb.trans hcap)
    (primitiveRowLift_prime q hprim (Or.inl hf))
    (primitiveRowLift_code_weight_of_two_sided q 131071 hf hs)
    (primitiveRowLift_value_weight_of_two_sided q hf hs) hidx.symm
    (fun i ↦ primitiveRowLift_germ_order_one q hprim (nodes i)
      (u₀ i) (v₀ i) (u₁ i) (v₁ i) (hgood i))
    (fun g ↦ P (seed g)) (fun g ↦ (P (seed g)).map σ) seed (fun g ↦ (seed g) ^ p) agreement
    hdegree (fun g ↦ Polynomial.natDegree_map_le.trans (hdegree g)) hsize h₀ h₁
  intro g
  exact (primitiveRowLift_specializes_eq σ p q P (seed g)).trans (hzero g)

end ProximityPrize.SubmissionLower.Koala6844HighOrdinary

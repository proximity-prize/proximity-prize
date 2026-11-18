import ProximityPrize.SubmissionLower.Koala6831SeparatedCarrier
import ProximityPrize.SubmissionLower.Koala6831SeparatedRow
import ProximityPrize.SubmissionLower.Koala6831OrdinaryGoodNode
import ProximityPrize.SubmissionLower.Koala6831PrimitivePrime
import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail

namespace ProximityPrize.SubmissionLower.Koala6831Separated

open MvPolynomial Koala6831Ordinary Koala6831Comparison Koala6831Quotient
open Koala6831Separation (NormalForm)
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

theorem exists_long_separated_carrier_of_primitive {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (q : SymbolicRow (SeedRing K)) (hprim : IsPrimitiveRow q)
    (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (long : 9554 ≤ primitiveExcess 131071 q) (small : primitiveExcess 131071 q ≤ 31357)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (hgood : ∀ i, q.atNode (MvPolynomial.C (nodes i))
      (MvPolynomial.C (u₀ i) + MvPolynomial.X 0 * MvPolynomial.C (v₀ i))
      (MvPolynomial.C (u₁ i) + MvPolynomial.X 1 * MvPolynomial.C (v₁ i)) = 0)
    (σ : K →+* K) (p : ℕ) (P : K → Polynomial K) (seed : Γ → K)
    (agreement : Γ → Finset I) (hdegree : ∀ g, (P (seed g)).natDegree ≤ 131071)
    (hsize : ∀ g, 181078 ≤ (agreement g).card)
    (h₀ : ∀ g i, i ∈ agreement g → (P (seed g)).eval (nodes i) = u₀ i + seed g * v₀ i)
    (h₁ : ∀ g i, i ∈ agreement g →
      ((P (seed g)).map σ).eval (nodes i) = u₁ i + (seed g) ^ p * v₁ i)
    (hzero : ∀ g, primitiveSelected σ p q P (seed g) = 0) :
    ∃ G : Carrier K, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 165 ∧
        d 0 + 131071 * d 1 ≤ 16 * 181078 - 1 + 22 * primitiveExcess 131071 q ∧
        d 0 + 131071 * d 1 < 2130706433) ∧
      ∀ g, Koala6831Intrinsic.graphSpecialize (P (seed g)) (seed g) ((seed g) ^ p) G = 0 := by
  let δ := primitiveExcess 131071 q
  obtain ⟨βL, aL, bL, βR, aR, bR⟩ := coefficient_block_caps N
  obtain ⟨qS, qL, qR⟩ := primitive_block_weights N hf hs
  have βcode : weightDegree (codeWeights 131071) (retainCarrier (carrierOfSeedCoefficients q.beta)) ≤ 131071 + δ := by
    rw [liftedCoefficient_code_weight]
    have h : q.beta.natDegree - 131071 ≤ δ := le_max_left _ _
    omega
  have acode : weightDegree (codeWeights 131071) (retainCarrier (carrierOfSeedCoefficients q.first)) ≤ δ := by
    rw [liftedCoefficient_code_weight]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have bcode : weightDegree (codeWeights 131071) (retainCarrier (carrierOfSeedCoefficients q.second)) ≤ δ := by
    rw [liftedCoefficient_code_weight]
    exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨G, hG, hcap, hgraph⟩ := exists_long_carrier nodes u₀ v₀ u₁ v₁ node_count
    (carrierOfSeedCoefficients q.beta) (carrierOfSeedCoefficients q.first)
    (carrierOfSeedCoefficients q.second) (carrierOfSeedCoefficients_ne_zero hs) δ long small
    (liftedCoefficient_value_weight q.beta) (liftedCoefficient_value_weight q.first)
    (liftedCoefficient_value_weight q.second) βL aL bL βR aR bR βcode acode bcode
    (primitiveRowLift_prime q hprim (Or.inl hf))
    (primitiveRowLift_code_weight_of_two_sided q 131071 hf hs)
    (primitiveRowLift_value_weight_of_two_sided q hf hs) qS qL qR
    (fun i ↦ primitiveRowLift_germ_order_one q hprim (nodes i)
      (u₀ i) (v₀ i) (u₁ i) (v₁ i) (hgood i))
    (fun g ↦ P (seed g)) (fun g ↦ (P (seed g)).map σ) seed (fun g ↦ (seed g) ^ p) agreement
    hdegree (fun g ↦ Polynomial.natDegree_map_le.trans (hdegree g)) hsize h₀ h₁
    (fun g ↦ (primitiveRowLift_specializes_eq σ p q P (seed g)).trans (hzero g))
  refine ⟨G, hG, ?_, ?_⟩
  · intro d hd
    obtain ⟨hy, ht, hz, hx⟩ := hcap d hd
    refine ⟨hy, ht, hz, hx, hx.trans_lt ?_⟩
    have hsδ : δ ≤ 31357 := small
    omega
  · exact hgraph

end

end ProximityPrize.SubmissionLower.Koala6831Separated

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

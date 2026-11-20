/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.LowerFoundation

namespace KoalaFactorResultant

open ProximityPrize.SubmissionLower
open RCN082 RCN136 RCN290 RCN293 RCN267
open scoped BigOperators

noncomputable section
variable {F E : Type*} [Field F] [Field E]
/-- The last Hasse variable occupies slot 2. The other two jet variables
occupy slots 1 and 3, so all three contribute one to jet weight. -/
def weights : Fin 4 → ℕ := ![0,1,1,1]

theorem eliminate_singular_and_account_factors
    (p U s : ℕ) [CharP F p] (hs : 1 ≤ s) (hp : s < p)
    (Q : MvPolynomial (Fin 4) F) (hQ : Q ≠ 0) (hT : Q.degreeOf 2 ≤ s)
    (hU : MvPolynomial.weightedTotalDegree weights Q ≤ U) :
    ∃ S : MvPolynomial (Fin 4) F, S ≠ 0 ∧ S.degreeOf 2 = 0 ∧
      MvPolynomial.weightedTotalDegree weights S ≤ (2*s-1)*U ∧
      (∑ H ∈ activeFactors Q, MvPolynomial.weightedTotalDegree weights H) ≤ U ∧
      ∀ (φ : Polynomial F →+* E), Function.Injective φ → ∀ v : Fin 3 → E,
        MvPolynomial.eval v (surfaceMap φ Q) = 0 →
        MvPolynomial.eval v (surfaceMap φ S) = 0 ∨
        ∃ H ∈ activeFactors Q, Irreducible H ∧ 0 < H.degreeOf 2 ∧
          MvPolynomial.eval v (surfaceMap φ H) = 0 ∧
          MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 H)) ≠ 0 := by
  classical
  refine ⟨singularAuxiliary Q,singularAuxiliary_nonzero Q hQ p (hT.trans_lt hp),
    singularAuxiliary_R_degree Q hQ p (hT.trans_lt hp),
    (singularAuxiliary_weight_le weights Q hQ s hs hT).trans (Nat.mul_le_mul_left _ hU), ?_, ?_⟩
  · exact (sum_weighted_degrees_le_of_prod_dvd weights (activeFactors Q) id Q hQ
      (activeFactors_product_dvd Q hQ)).trans hU
  · intro φ hφ v hv
    exact surface_zero_singular_or_regular φ hφ Q hQ v hv

/-- Pooling the regular factor charges costs no more than one degree-U stage. -/
theorem sum_regular_cost {I : Type*} (H : Finset I) (j : I → ℕ) (U K : ℕ)
    (h : ∑ i ∈ H, j i ≤ U) :
    ∑ i ∈ H, j i*(1+2*K*(j i-1))^2 ≤ U*(1+2*K*(U-1))^2 := by
  calc
    _ ≤ ∑ i ∈ H, j i*(1+2*K*(U-1))^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hj : j i ≤ U := (Finset.single_le_sum (f:=j) (fun _ _ => Nat.zero_le _) hi).trans h
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hj 1)) 1) _)
    _ = (∑ i ∈ H, j i)*(1+2*K*(U-1))^2 := by rw [Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ h

#print axioms eliminate_singular_and_account_factors
#print axioms sum_regular_cost
end
end KoalaFactorResultant

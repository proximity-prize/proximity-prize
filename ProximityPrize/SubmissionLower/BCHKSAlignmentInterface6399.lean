import ProximityPrize.SubmissionLower.BCHKSInterpolation6399
import ProximityPrize.SubmissionLower.BCHKSParameters6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open BCHKSSubstitutionVanish

/-- Exact remaining algebraic statement after the concrete interpolation and
root-multiplicity steps.  All analytic, MCA, Johnson, and score bookkeeping is
outside this interface. -/
def BCHKSPolynomialAlignment6399 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field) (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↥S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field))),
    bchksNumerator6399 < S.card →
    Q ≠ 0 →
    (∀ z : ↥S, (P z).natDegree ≤ 131071) →
    (∀ z : ↥S, 185374 ≤ (A z.1).card) →
    (∀ z : ↥S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) →
    (∀ z : ↥S, triEval Q z.1 (P z) = 0) →
    (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      j < 5280 ∧ a + 131071 * j < 692001142 ∧
        ((Q.coeff j).coeff a).natDegree + j < 13141403) →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field, ∃ T : Finset IRSProfile.Field,
      ∃ hTS : T ⊆ S, bchksErrors6399 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

private lemma degree_lt_baseDimension_of_natDegree_le
    {p : Polynomial IRSProfile.Field} (hp : p.natDegree ≤ 131071) :
    p.degree < (IRSProfile.baseDimension : WithBot ℕ) := by
  by_cases hzero : p = 0
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
    norm_num [IRSProfile.baseDimension]
    omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The sole algebraic interface above implies the exact alignment predicate
consumed by the completed MCA/soundness pipeline. -/
theorem alignmentBound6399_of_polynomialAlignment
    (halg : BCHKSPolynomialAlignment6399) :
    AffineLineAlignmentBound IRSProfile.baseCode bchksErrors6399 bchksNumerator6399 := by
  classical
  intro U S A hS hA hcomb
  have hA' : ∀ z ∈ S, 185374 ≤ (A z).card := by
    intro z hz
    have h := hA z hz
    norm_num [IRSProfile.Index, bchksErrors6399] at h
    exact h
  obtain ⟨P, Q, hQ, hPdeg, hPagree, hQvan, hcaps⟩ :=
    exists_bchks_interpolant_vanishing6399 U S A hA' hcomb
  obtain ⟨p₀, p₁, T, hTS, hTcard, hp₀deg, hp₁deg, hline⟩ :=
    halg U S A P Q hS hQ hPdeg (fun z => hA' z z.property) hPagree hQvan hcaps
  let p : Fin 2 → IRSProfile.Index → IRSProfile.Field := fun j =>
    ReedSolomon.evalOnPoints IRSProfile.domain (if j = 0 then p₀ else p₁)
  refine ⟨p, ?_, T, hTS, hTcard, ?_⟩
  · intro j
    change p j ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    fin_cases j
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le hp₀deg
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le hp₁deg
  · intro z hz x hx
    have hagree := hPagree ⟨z, hTS hz⟩ x hx
    have hpoly := congrArg (Polynomial.eval (IRSProfile.domain x))
      (hline z hz)
    simp [p, ReedSolomon.evalOnPoints] at hpoly
    rw [← hagree]
    simpa [p, ReedSolomon.evalOnPoints, mul_add, add_mul] using hpoly

end ProximityPrize.SubmissionLower


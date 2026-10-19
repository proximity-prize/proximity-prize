import ProximityPrize.SubmissionBinaryLower.BCHKSInterpolation
import ProximityPrize.SubmissionBinaryLower.BCHKSParameters

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open BCHKSSubstitutionVanish

/-- Exact remaining algebraic statement after the concrete interpolation and
root-multiplicity steps.  All analytic, MCA, Johnson, and score bookkeeping is
outside this interface. -/
def BCHKSPolynomialAlignment : Prop :=
  ∀ (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (S : Finset BinaryIRSProfile.Field) (A : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (P : ↥S → Polynomial BinaryIRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial BinaryIRSProfile.Field))),
    bchksNumerator < S.card →
    Q ≠ 0 →
    (∀ z : ↥S, (P z).natDegree ≤ 1048575) →
    (∀ z : ↥S, 1484152 ≤ (A z.1).card) →
    (∀ z : ↥S, ∀ i ∈ A z,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) →
    (∀ z : ↥S, triEval Q z.1 (P z) = 0) →
    (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      j < 312 ∧ a + 1048575 * j < 326513440 ∧
        ((Q.coeff j).coeff a).natDegree + j < 87534) →
    ∃ p₀ p₁ : Polynomial BinaryIRSProfile.Field, ∃ T : Finset BinaryIRSProfile.Field,
      ∃ hTS : T ⊆ S, bchksErrors + 1 < T.card ∧
      p₀.natDegree ≤ 1048575 ∧ p₁.natDegree ≤ 1048575 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

private lemma degree_lt_baseDimension_of_natDegree_le
    {p : Polynomial BinaryIRSProfile.Field} (hp : p.natDegree ≤ 1048575) :
    p.degree < (BinaryIRSProfile.baseDimension : WithBot ℕ) := by
  by_cases hzero : p = 0
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
    norm_num [BinaryIRSProfile.baseDimension]
    omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The sole algebraic interface above implies the exact alignment predicate
consumed by the completed MCA/soundness pipeline. -/
theorem alignmentBound_of_polynomialAlignment
    (halg : BCHKSPolynomialAlignment) :
    AffineLineAlignmentBound BinaryIRSProfile.baseCode bchksErrors bchksNumerator := by
  classical
  intro U S A hS hA hcomb
  have hA' : ∀ z ∈ S, 1484152 ≤ (A z).card := by
    intro z hz
    have h := hA z hz
    rw [BinaryIRSProfile.card_index] at h
    simpa [bchksErrors] using h
  obtain ⟨P, Q, hQ, hPdeg, hPagree, hQvan, hcaps⟩ :=
    exists_bchks_interpolant_vanishing U S A hA' hcomb
  obtain ⟨p₀, p₁, T, hTS, hTcard, hp₀deg, hp₁deg, hline⟩ :=
    halg U S A P Q hS hQ hPdeg (fun z => hA' z z.property) hPagree hQvan hcaps
  let p : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field := fun j =>
    ReedSolomon.evalOnPoints BinaryIRSProfile.domain (if j = 0 then p₀ else p₁)
  refine ⟨p, ?_, T, hTS, hTcard, ?_⟩
  · intro j
    change p j ∈ ReedSolomon.code BinaryIRSProfile.domain BinaryIRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    fin_cases j
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le hp₀deg
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le hp₁deg
  · intro z hz x hx
    have hagree := hPagree ⟨z, hTS hz⟩ x hx
    have hpoly := congrArg (Polynomial.eval (BinaryIRSProfile.domain x))
      (hline z hz)
    simp [p, ReedSolomon.evalOnPoints] at hpoly
    rw [← hagree]
    simpa [p, ReedSolomon.evalOnPoints, mul_add, add_mul] using hpoly

end ProximityPrize.SubmissionBinaryLower

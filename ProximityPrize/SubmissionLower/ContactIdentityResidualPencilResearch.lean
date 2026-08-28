import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualPolynomialResearch
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence

/-!
# Agreement and pencil transport for actual-identity residuals

This file supplies the two incidence-facing consequences of the exact nodal
normal form: agreements outside the identity set descend to the residual
polynomial, and a large residual affine pencil would lift to a forbidden
large affine pencil of the original degree-`w` selected family.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualPencilResearch

open ContactPrimeSeedIncidence

noncomputable section

variable {K ι : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

theorem nodal_eval_ne_zero_of_mem_sdiff
    (I nodes : Finset ι) (x : ι → K)
    (hsub : I ⊆ nodes) (hinj : Set.InjOn x nodes)
    {j : ι} (hj : j ∈ nodes \ I) :
    (Lagrange.nodal I x).eval (x j) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro i hi hji
  have hji' : j = i := hinj (Finset.mem_sdiff.mp hj).1 (hsub hi) hji
  exact (Finset.mem_sdiff.mp hj).2 (hji' ▸ hi)

def residualReceived
    (I : Finset ι) (x u : ι → K) (P : Polynomial K) (j : ι) : K :=
  (u j - P.eval (x j)) / (Lagrange.nodal I x).eval (x j)

/-- Outside the actual identity set, dividing the original agreement by the
nonzero nodal value gives an exact residual agreement. -/
theorem residual_agreement_of_original
    (I nodes : Finset ι) (x u0 u1 : ι → K)
    (hsub : I ⊆ nodes) (hinj : Set.InjOn x nodes)
    (P0 P1 C S : Polynomial K) (gamma : K)
    (hnormal : S = P0 + Polynomial.C gamma * P1 + Lagrange.nodal I x * C)
    {j : ι} (hj : j ∈ nodes \ I)
    (hagree : S.eval (x j) = u0 j + gamma * u1 j) :
    C.eval (x j) = residualReceived I x u0 P0 j +
      gamma * residualReceived I x u1 P1 j := by
  have hV := nodal_eval_ne_zero_of_mem_sdiff I nodes x hsub hinj hj
  have heval := congrArg (fun P : Polynomial K ↦ P.eval (x j)) hnormal
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at heval
  unfold residualReceived
  field_simp [hV]
  linear_combination hagree - heval

/-- A residual affine pencil lifts through the nodal normal form to an
original affine pencil of degree at most `w`. -/
theorem noLargeSelectedPencil_residual
    (I : Finset ι) (x : ι → K) (w e : ℕ) (hIw : I.card ≤ w)
    (selected residual : K → Polynomial K) (Gamma : Finset K)
    (P0 P1 : Polynomial K) (hP0 : P0.natDegree ≤ w)
    (hP1 : P1.natDegree ≤ w)
    (hnormal : ∀ gamma ∈ Gamma,
      selected gamma = P0 + Polynomial.C gamma * P1 +
        Lagrange.nodal I x * residual gamma)
    (hno : NoLargeSelectedPencil selected Gamma w e) :
    NoLargeSelectedPencil residual Gamma (w - I.card) e := by
  intro A B hA hB
  let V := Lagrange.nodal I x
  let A0 := P0 + V * A
  let B0 := P1 + V * B
  have hV : V.natDegree = I.card := by
    exact Lagrange.natDegree_nodal
  have hVA : (V * A).natDegree ≤ w := by
    calc
      (V * A).natDegree ≤ V.natDegree + A.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ I.card + (w - I.card) := by omega
      _ = w := Nat.add_sub_of_le hIw
  have hVB : (V * B).natDegree ≤ w := by
    calc
      (V * B).natDegree ≤ V.natDegree + B.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ I.card + (w - I.card) := by omega
      _ = w := Nat.add_sub_of_le hIw
  have hA0 : A0.natDegree ≤ w := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le hP0 hVA)
  have hB0 : B0.natDegree ≤ w := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le hP1 hVB)
  calc
    (Gamma.filter (fun gamma ↦
      residual gamma = A + Polynomial.C gamma * B)).card ≤
        (Gamma.filter (fun gamma ↦
          selected gamma = A0 + Polynomial.C gamma * B0)).card := by
      apply Finset.card_le_card
      intro gamma hgamma
      obtain ⟨hGamma, hpencil⟩ := Finset.mem_filter.mp hgamma
      apply Finset.mem_filter.mpr
      refine ⟨hGamma, ?_⟩
      rw [hnormal gamma hGamma, hpencil]
      simp only [A0, B0, V]
      ring
    _ ≤ e + 1 := hno A0 B0 hA0 hB0

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualPencilResearch

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualPencilResearch.residual_agreement_of_original
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualPencilResearch.noLargeSelectedPencil_residual

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualPolynomialResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualPencilResearch

/-!
# One common residual family on an actual identity set

The pointwise residual theorem chooses the same Lagrange pencil in its proof,
but its existential interface does not expose that uniformity.  Nested
incidence needs one common `P0`, `P1`, and nodal factor for the complete seed
family.  This module packages precisely that family-level normal form and its
agreement/no-large-pencil consequences.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualFamilyResearch

open ContactPrimeSeedIncidence
open ContactIdentityResidualPolynomialResearch
open ContactIdentityResidualPencilResearch

noncomputable section

variable {K ι : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

/-- A single base-field Lagrange pencil and a single residual-polynomial
function work simultaneously for every seed in `Gamma`. -/
theorem exists_common_affine_nodal_residual_family
    (I : Finset ι) (x u0 u1 : ι → K)
    (w : ℕ) (hIw : I.card ≤ w) (hinj : Set.InjOn x I)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hvalues : ∀ gamma ∈ Gamma, ∀ i ∈ I,
      (selected gamma).eval (x i) = u0 i + gamma * u1 i) :
    ∃ P0 P1 : Polynomial K, ∃ residual : K → Polynomial K,
      P0.natDegree ≤ w ∧ P1.natDegree ≤ w ∧
      (∀ gamma ∈ Gamma, (residual gamma).natDegree ≤ w - I.card) ∧
      ∀ gamma ∈ Gamma,
        selected gamma = P0 + Polynomial.C gamma * P1 +
          Lagrange.nodal I x * residual gamma := by
  classical
  let P0 : Polynomial K := Lagrange.interpolate I x u0
  let P1 : Polynomial K := Lagrange.interpolate I x u1
  let V : Polynomial K := Lagrange.nodal I x
  let D : K → Polynomial K := fun gamma ↦
    selected gamma - (P0 + Polynomial.C gamma * P1)
  have hpredw : I.card - 1 ≤ w := (Nat.sub_le I.card 1).trans hIw
  have hP0 : P0.natDegree ≤ w := by
    apply Polynomial.natDegree_le_of_degree_le
    exact (Lagrange.degree_interpolate_le u0 hinj).trans
      (WithBot.coe_le_coe.mpr hpredw)
  have hP1 : P1.natDegree ≤ w := by
    apply Polynomial.natDegree_le_of_degree_le
    exact (Lagrange.degree_interpolate_le u1 hinj).trans
      (WithBot.coe_le_coe.mpr hpredw)
  have hDdegree : ∀ gamma ∈ Gamma, (D gamma).natDegree ≤ w := by
    intro gamma hgamma
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (hdegree gamma hgamma)
      ((Polynomial.natDegree_add_le _ _).trans
        (max_le hP0 ((Polynomial.natDegree_C_mul_le gamma P1).trans hP1)))
  have hDeval : ∀ gamma ∈ Gamma, ∀ i ∈ I,
      (D gamma).eval (x i) = 0 := by
    intro gamma hgamma i hi
    simp only [D, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
      Lagrange.eval_interpolate_at_node u1 hinj hi,
      hvalues gamma hgamma i hi]
    ring
  have hdvd : ∀ gamma, gamma ∈ Gamma → V ∣ D gamma := by
    intro gamma hgamma
    exact nodal_dvd_of_eval_eq_zero I x hinj (D gamma)
      (hDeval gamma hgamma)
  let residual : K → Polynomial K := fun gamma ↦
    if hgamma : gamma ∈ Gamma then (hdvd gamma hgamma).choose else 0
  have hfactor : ∀ gamma ∈ Gamma,
      D gamma = V * residual gamma := by
    intro gamma hgamma
    dsimp only [residual]
    rw [dif_pos hgamma]
    exact (hdvd gamma hgamma).choose_spec
  have hresidualDegree : ∀ gamma ∈ Gamma,
      (residual gamma).natDegree ≤ w - I.card := by
    intro gamma hgamma
    by_cases hzero : residual gamma = 0
    · simp [hzero]
    · have hdegmul : (V * residual gamma).natDegree =
          I.card + (residual gamma).natDegree := by
        rw [(Lagrange.nodal_monic (s := I) (v := x)).natDegree_mul' hzero,
          Lagrange.natDegree_nodal]
      have hmul : (V * residual gamma).natDegree ≤ w := by
        rw [← hfactor gamma hgamma]
        exact hDdegree gamma hgamma
      rw [hdegmul] at hmul
      omega
  refine ⟨P0, P1, residual, hP0, hP1, hresidualDegree, ?_⟩
  intro gamma hgamma
  have hf := hfactor gamma hgamma
  change selected gamma = P0 + Polynomial.C gamma * P1 + V * residual gamma
  change selected gamma - (P0 + Polynomial.C gamma * P1) =
    V * residual gamma at hf
  linear_combination hf

/-- Consumer package: the common residual family simultaneously preserves
all nonidentity agreements and inherits the original no-large-pencil bound. -/
theorem exists_residual_family_with_incidence_data
    (I nodes : Finset ι) (x u0 u1 : ι → K)
    (w e : ℕ) (hsub : I ⊆ nodes) (hIw : I.card ≤ w)
    (hinj : Set.InjOn x nodes)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hvalues : ∀ gamma ∈ Gamma, ∀ i ∈ I,
      (selected gamma).eval (x i) = u0 i + gamma * u1 i)
    (hno : NoLargeSelectedPencil selected Gamma w e) :
    ∃ P0 P1 : Polynomial K, ∃ residual : K → Polynomial K,
      P0.natDegree ≤ w ∧ P1.natDegree ≤ w ∧
      (∀ gamma ∈ Gamma, (residual gamma).natDegree ≤ w - I.card) ∧
      NoLargeSelectedPencil residual Gamma (w - I.card) e ∧
      (∀ gamma ∈ Gamma,
        selected gamma = P0 + Polynomial.C gamma * P1 +
          Lagrange.nodal I x * residual gamma) ∧
      ∀ gamma ∈ Gamma, ∀ j ∈ nodes \ I,
        (selected gamma).eval (x j) = u0 j + gamma * u1 j →
          (residual gamma).eval (x j) =
            residualReceived (K := K) I x u0 P0 j +
              gamma * residualReceived (K := K) I x u1 P1 j := by
  have hIinj : Set.InjOn x I := hinj.mono hsub
  obtain ⟨P0, P1, residual, hP0, hP1, hresdeg, hnormal⟩ :=
    exists_common_affine_nodal_residual_family I x u0 u1 w hIw hIinj
      selected Gamma hdegree hvalues
  have hnores : NoLargeSelectedPencil residual Gamma (w - I.card) e :=
    noLargeSelectedPencil_residual I x w e hIw selected residual Gamma
      P0 P1 hP0 hP1 hnormal hno
  refine ⟨P0, P1, residual, hP0, hP1, hresdeg, hnores, hnormal, ?_⟩
  intro gamma hgamma j hj hagree
  exact residual_agreement_of_original I nodes x u0 u1 hsub hinj
    P0 P1 (residual gamma) (selected gamma) gamma
    (hnormal gamma hgamma) hj hagree

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualFamilyResearch

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualFamilyResearch.exists_common_affine_nodal_residual_family
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualFamilyResearch.exists_residual_family_with_incidence_data

import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401

/-!
# Linear-algebra interface for the two-lane key-equation failure branch

This file separates the routine rank-deficiency argument from the one
benchmark-specific Vandermonde-duality statement still required by the
two-lane syndrome route.

For a stacked key matrix `M`, rank below the number of error columns gives a
literal nonzero right-kernel vector `v`.  The standard dual-RS factorization
is exposed by `TwoLaneKernelPolynomialization6401`: it turns the two weighted
error lanes of every kernel vector into evaluations of polynomials of degree
at most `22507`, with one common nonzero barycentric weight.  Once that
interface is supplied, cancellation-free multiplication gives exactly
`TwoLaneFailureRelation`, and the ordinary polynomial is nonzero whenever
the selected error values are nonzero.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusKeyEquationKernelBridge6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusKeyEquationFork6401

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

/-- Rank deficiency below the full column count supplies a nonzero right
kernel vector.  This form works for the full stacked (rectangular) two-lane
matrix, not merely for one selected square minor. -/
theorem exists_nonzero_mulVec_eq_zero_of_rank_lt_card
    {F Row Col : Type*} [Field F]
    [Fintype Row] [Fintype Col]
    (M : Matrix Row Col F)
    (hrank : M.rank < Fintype.card Col) :
    ∃ v : Col → F, v ≠ 0 ∧ M.mulVecLin v = 0 := by
  have hnull :=
    BCHKSGaoSpecializationCore6400.rank_add_finrank_ker_mulVecLin M
  have hkerpos :
      0 < Module.finrank F (LinearMap.ker M.mulVecLin) := by
    omega
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hbot
    have hzero :
        Module.finrank F (LinearMap.ker M.mulVecLin) = 0 := by
      rw [hbot]
      simp
    omega
  obtain ⟨v, hvker, hvne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hvne, ?_⟩
  exact LinearMap.mem_ker.mp hvker

/-- Exact output expected from the standard dual-Vandermonde factorization
of the two syndrome lanes.  The common `weight` is the inverse derivative of
the error locator in the usual construction. -/
structure TwoLaneKernelPolynomialization6401
    {F ι Row : Type*} [Field F]
    [Fintype ι] [Fintype Row]
    (sigma : F →+* F) (alpha : ι → F) (E : ι → F)
    (M : Matrix Row ι F) where
  weight : ι → F
  weight_ne_zero : ∀ i, weight i ≠ 0
  polynomialize : ∀ v : ι → F, M.mulVecLin v = 0 →
    ∃ W₀ W₁ : Polynomial F,
      W₀.natDegree ≤ keySecondLaneRows6401 - 1 ∧
      W₁.natDegree ≤ keySecondLaneRows6401 - 1 ∧
      (∀ i, W₀.eval (alpha i) = weight i * v i * E i) ∧
      (∀ i, W₁.eval (alpha i) = weight i * v i * sigma (E i))

/-- The common-weight evaluation representation implies the failure relation
without division by an error value or a barycentric weight. -/
theorem twoLaneFailureRelation_of_polynomialized_kernel
    {F ι : Type*} [Field F]
    (sigma : F →+* F) (alpha : ι → F) (E weight v : ι → F)
    (W₀ W₁ : Polynomial F)
    (hW₀ : ∀ i, W₀.eval (alpha i) = weight i * v i * E i)
    (hW₁ : ∀ i, W₁.eval (alpha i) = weight i * v i * sigma (E i)) :
    TwoLaneFailureRelation sigma alpha E W₀ W₁ := by
  intro i
  rw [hW₀ i, hW₁ i]
  ring

/-- End-to-end bounded algebraic failure fork.  The only substantive input
left to the syndrome construction is `H`, the dual-Vandermonde
polynomialization interface. -/
theorem exists_failureRelation_of_rank_lt_card
    {F ι Row : Type*} [Field F]
    [Fintype ι] [Fintype Row]
    (sigma : F →+* F) (alpha : ι → F) (E : ι → F)
    (M : Matrix Row ι F)
    (H : TwoLaneKernelPolynomialization6401 sigma alpha E M)
    (hE : ∀ i, E i ≠ 0)
    (hrank : M.rank < Fintype.card ι) :
    ∃ W₀ W₁ : Polynomial F,
      W₀ ≠ 0 ∧
      W₀.natDegree ≤ keySecondLaneRows6401 - 1 ∧
      W₁.natDegree ≤ keySecondLaneRows6401 - 1 ∧
      TwoLaneFailureRelation sigma alpha E W₀ W₁ := by
  obtain ⟨v, hvne, hvker⟩ :=
    exists_nonzero_mulVec_eq_zero_of_rank_lt_card M hrank
  obtain ⟨W₀, W₁, hW₀deg, hW₁deg, hW₀eval, hW₁eval⟩ :=
    H.polynomialize v hvker
  have hW₀ne : W₀ ≠ 0 := by
    intro hzero
    apply hvne
    funext i
    have hi := hW₀eval i
    rw [hzero, Polynomial.eval_zero] at hi
    have hprod : H.weight i * v i * E i = 0 := hi.symm
    rcases mul_eq_zero.mp hprod with hleft | hEi
    · rcases mul_eq_zero.mp hleft with hwi | hvi
      · exact (H.weight_ne_zero i hwi).elim
      · exact hvi
    · exact (hE i hEi).elim
  exact ⟨W₀, W₁, hW₀ne, hW₀deg, hW₁deg,
    twoLaneFailureRelation_of_polynomialized_kernel
      sigma alpha E H.weight v W₀ W₁ hW₀eval hW₁eval⟩

/-- The numerical degree in the interface is literally the primitive
denominator cap `22507`. -/
theorem polynomialization_degree_exact6401 :
    keySecondLaneRows6401 - 1 = 22507 := by
  norm_num [keySecondLaneRows6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401, n6401,
    ownerDegreeCap6401, bchksErrors6401]

end BCHKSFrobeniusKeyEquationKernelBridge6401
end ProximityPrize.SubmissionLower

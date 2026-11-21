import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import ProximityPrize.SubmissionLower.KoalaRuledEmbedding
import ProximityPrize.SubmissionLower.KoalaWeightedDegree

set_option autoImplicit false

namespace SplitCut.Rect
noncomputable section
open MvPolynomial

variable {F : Type*} [Field F]

def axisWeights : Fin 4 → ℕ := ![1,2,0,0]

abbrev ordinateWeight (p : Ring F) : ℕ := p.weightedTotalDegree axisWeights

theorem weight_exponent (m : Exp) : Finsupp.weight axisWeights m = m 0 + 2*m 1 := by
  rw [Finsupp.weight_eq_sum]
  simp [axisWeights, Fin.sum_univ_succ, nsmul_eq_mul, Nat.mul_comm]

theorem mem_space {p : Ring F} {d : Box} :
    p ∈ space F d ↔ p.degreeOf 1 ≤ d.velocity ∧ ordinateWeight p ≤ d.base+2*d.velocity ∧
      p.degreeOf 2 ≤ d.seed₀ ∧ p.degreeOf 3 ≤ d.seed₁ := by
  simp only [degreeOf_le_iff, ordinateWeight, weightedTotalDegree, Finset.sup_le_iff, weight_exponent]
  exact ⟨fun h => ⟨fun _ hm => (h hm).1, fun _ hm => (h hm).2.1, fun _ hm => (h hm).2.2.1,
      fun _ hm => (h hm).2.2.2⟩,
    fun ⟨h₁,h₀,h₂,h₃⟩ _ hm => ⟨h₁ _ hm, h₀ _ hm, h₂ _ hm, h₃ _ hm⟩⟩

def rootShift (d : Box) (g : Ring F) : Box :=
  ⟨d.base-ordinateWeight g, d.velocity, d.seed₀-g.degreeOf 2, d.seed₁-g.degreeOf 3⟩

theorem root_mul_mem_iff {g p : Ring F} (hg : g ≠ 0) (hv : g.degreeOf 1 = 0)
    {d : Box} (h₀ : ordinateWeight g ≤ d.base) (h₂ : g.degreeOf 2 ≤ d.seed₀)
    (h₃ : g.degreeOf 3 ≤ d.seed₁) :
    g*p ∈ space F d ↔ p ∈ space F (rootShift d g) := by
  by_cases hp : p = 0
  · simp only [hp, mul_zero, Submodule.zero_mem]
  rw [mem_space, mem_space, degreeOf_mul_eq (n:=1) hg hp, degreeOf_mul_eq (n:=2) hg hp,
    degreeOf_mul_eq (n:=3) hg hp]
  change _ ≤ d.velocity ∧ (g*p).weightedTotalDegree axisWeights ≤ _ ∧ _ ↔ _
  rw [weighted_degree_mul axisWeights hg hp]
  simp only [rootShift, ordinateWeight, hv, Nat.zero_add]
  change g.weightedTotalDegree axisWeights ≤ d.base at h₀
  omega

/-- The kernel of the root quotient on a large box consists of the exact shifted box of multiples. -/
theorem root_piece_rank {g : Ring F} (hg : g ≠ 0) (hv : g.degreeOf 1 = 0)
    {d : Box} (h₀ : ordinateWeight g ≤ d.base) (h₂ : g.degreeOf 2 ≤ d.seed₀)
    (h₃ : g.degreeOf 3 ≤ d.seed₁) :
    Module.finrank F (piece (Ideal.span {g}) d) +
      Module.finrank F (space F (rootShift d g)) = Module.finrank F (space F d) := by
  let I : Ideal (Ring F) := Ideal.span {g}
  let M := space F d
  let M' := space F (rootShift d g)
  let π := (Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict M
  have hmul : ∀ p ∈ M', g*p ∈ M := fun _ hp => (root_mul_mem_iff hg hv h₀ h₂ h₃).mpr hp
  let μ : M' →ₗ[F] M := ((LinearMap.mulLeft F g).domRestrict M').codRestrict M fun p => hmul _ p.2
  have hinj : Function.Injective μ := fun p q h => Subtype.ext
    (mul_left_cancel₀ hg (congrArg Subtype.val h))
  have hker : LinearMap.range μ = LinearMap.ker π := by
    apply le_antisymm
    · rintro _ ⟨p,rfl⟩
      rw [LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · intro x hx
      have hI : x.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
      obtain ⟨p,hp⟩ := Ideal.mem_span_singleton.mp hI
      have hm : g*p ∈ M := hp ▸ x.2
      exact ⟨⟨p,(root_mul_mem_iff hg hv h₀ h₂ h₃).mp hm⟩, Subtype.ext hp.symm⟩
  have hdim := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, ← hker, LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

#print axioms root_piece_rank
end
end SplitCut.Rect

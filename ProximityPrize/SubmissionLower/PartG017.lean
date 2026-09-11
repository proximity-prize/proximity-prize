import ProximityPrize.SubmissionLower.PartG016


section Compact_FiniteMonomials
/-! Finite coefficient families embedded into a multivariate polynomial ring. -/
namespace ProximityPrize.SubmissionLower.FiniteMonomials
open scoped BigOperators
noncomputable section
set_option autoImplicit false
variable {K σ I : Type*} [Field K] [Fintype I]
local instance : DecidableEq σ := Classical.decEq σ
local instance : DecidableEq I := Classical.decEq I

def reconstruct (e : I → σ →₀ ℕ) : (I → K) →ₗ[K] MvPolynomial σ K :=
  ∑ i, (MvPolynomial.monomial (e i)).comp (LinearMap.proj i)

theorem reconstruct_apply (e : I → σ →₀ ℕ) (c : I → K) :
    reconstruct e c = ∑ i, MvPolynomial.monomial (e i) (c i) := by
  simp [reconstruct]

theorem coeff_reconstruct (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (c : I → K) (i : I) : MvPolynomial.coeff (e i) (reconstruct e c) = c i := by
  classical
  rw [reconstruct_apply, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, he.eq_iff]
  simp

theorem reconstruct_injective (e : I → σ →₀ ℕ) (he : Function.Injective e) :
    Function.Injective (reconstruct (K := K) e) := by
  intro c d h
  funext i
  have hh := congrArg (MvPolynomial.coeff (e i)) h
  simpa only [coeff_reconstruct e he] using hh

theorem coeff_reconstruct_of_notmem (e : I → σ →₀ ℕ) (c : I → K)
    (d : σ →₀ ℕ) (hd : d ∉ Set.range e) :
    MvPolynomial.coeff d (reconstruct e c) = 0 := by
  classical
  rw [reconstruct_apply, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_monomial, if_neg (fun h => hd ⟨i,h⟩)]

theorem mem_range_iff (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (P : MvPolynomial σ K) : P ∈ (reconstruct (K := K) e).range ↔
      ∀ d ∈ P.support, d ∈ Set.range e := by
  classical
  constructor
  · rintro ⟨c,rfl⟩ d hd
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hd (coeff_reconstruct_of_notmem e c d hn)
  · intro h
    refine ⟨fun i => P.coeff (e i), ?_⟩
    ext d
    by_cases hd : d ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hd
      exact coeff_reconstruct e he _ i
    · rw [coeff_reconstruct_of_notmem e _ d hd]
      exact (MvPolynomial.notMem_support_iff.mp (fun hs => hd (h d hs))).symm


end
end ProximityPrize.SubmissionLower.FiniteMonomials

end Compact_FiniteMonomials

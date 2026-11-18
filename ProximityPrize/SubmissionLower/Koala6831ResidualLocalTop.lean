import ProximityPrize.SubmissionLower.LowerGeometry
import Mathlib.LinearAlgebra.StdBasis

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open scoped BigOperators

noncomputable section

variable {K I V : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module K V]

theorem finrank_contact_le_subspace_add_active (T : (I → K) →ₗ[K] V)
    (W : Submodule K V) [FiniteDimensional K W]
    (active : I → Prop) [DecidablePred active]
    (hi : ∀ i, ¬ active i → T (Pi.single i (1 : K)) ∈ W) :
    Module.finrank K T.range ≤ Module.finrank K W + Fintype.card {i : I // active i} := by
  let b : {i : I // active i} → V := fun i => T (Pi.single i.val (1 : K))
  let A := Submodule.span K (Set.range b)
  let _ : FiniteDimensional K A := FiniteDimensional.span_of_finite K (Set.finite_range b)
  have hle : T.range ≤ W ⊔ A := by
    rintro _ ⟨c,rfl⟩
    rw [← (Pi.basisFun K I).sum_repr c, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, Pi.basisFun_apply]
    apply Submodule.smul_mem
    by_cases h : active i
    · apply (show A ≤ W ⊔ A from le_sup_right)
      exact Submodule.subset_span ⟨⟨i,h⟩,rfl⟩
    · exact (show W ≤ W ⊔ A from le_sup_left) (hi i h)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W A
  have hr : Module.finrank K (W ⊔ A : Submodule K V) ≤
      Module.finrank K W + Module.finrank K A := by omega
  exact (Submodule.finrank_mono hle).trans
    (hr.trans (Nat.add_le_add_left (finrank_range_le_card b) _))

theorem exists_kernel_of_lower_rank (T : (I → K) →ₗ[K] V)
    (W : Submodule K V) [FiniteDimensional K W]
    (active : I → Prop) [DecidablePred active]
    (hi : ∀ i, ¬ active i → T (Pi.single i (1 : K)) ∈ W)
    (budget : ℕ) (hlo : Module.finrank K W ≤ budget)
    (hgap : budget + Fintype.card {i : I // active i} < Fintype.card I) :
    ∃ c : I → K, c ≠ 0 ∧ T c = 0 := by
  have hr := finrank_contact_le_subspace_add_active T W active hi
  have hsum := T.finrank_range_add_finrank_ker
  have hdim : Module.finrank K (I → K) = Fintype.card I := by simp
  have hk : 0 < Module.finrank K T.ker := by omega
  have hne : T.ker ≠ ⊥ := by
    intro h
    rw [h] at hk
    simp at hk
  obtain ⟨c,hc,hc0⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨c,hc0,LinearMap.mem_ker.mp hc⟩

section Interpolant

open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetGlobalMap (coefficientLocal untruncate_contact)

variable {N : Type*}

def globalContactMap (e : I → Fin 5 →₀ ℕ) (m : ℕ) (x u0 u1 : N → K) :
    (I → K) →ₗ[K] (N → SecondJetLocal.Target (K := K)) :=
  LinearMap.pi fun n => (SecondJetRank.contactMap (K := K) m).comp
    (coefficientLocal e m (x n) (u0 n) (u1 n))

theorem globalContactMap_single (e : I → Fin 5 →₀ ℕ) (m : ℕ) (x u0 u1 : N → K)
    (i : I) (n : N) : globalContactMap e m x u0 u1 (Pi.single i (1 : K)) n =
      SecondJetRank.contactMap (K := K) m (truncateOuter (K := K) m
        (flatEquiv (K := K) (localize (x n) (u0 n) (u1 n)
          (MvPolynomial.monomial (e i) (1 : K))))) := by
  have hsum : FiniteMonomials.reconstruct e (Pi.single i (1 : K)) =
      MvPolynomial.monomial (e i) (1 : K) := by
    rw [FiniteMonomials.reconstruct_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  change SecondJetRank.contactMap (K := K) m (truncateOuter (K := K) m
    (flatEquiv (K := K) (localize (x n) (u0 n) (u1 n)
      (FiniteMonomials.reconstruct e (Pi.single i (1 : K)))))) = _
  rw [hsum]

theorem exists_global_contact_of_inactive_mem
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m : ℕ) (x u0 u1 : N → K)
    (W : Submodule K (N → SecondJetLocal.Target (K := K))) [FiniteDimensional K W]
    (active : I → Prop) [DecidablePred active]
    (hi : ∀ i, ¬ active i →
      globalContactMap e m x u0 u1 (Pi.single i (1 : K)) ∈ W)
    (budget : ℕ) (hlo : Module.finrank K W ≤ budget)
    (hgap : budget + Fintype.card {i : I // active i} < Fintype.card I) :
    ∃ P : Poly (K := K), P ≠ 0 ∧ (∀ d ∈ P.support, d ∈ Set.range e) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (flatEquiv (K := K) (localize (x n) (u0 n) (u1 n) P)) := by
  obtain ⟨c,hc,hzero⟩ := exists_kernel_of_lower_rank (globalContactMap e m x u0 u1)
    W active hi budget hlo hgap
  refine ⟨FiniteMonomials.reconstruct e c, ?_, ?_, ?_⟩
  · intro hz
    apply hc
    apply FiniteMonomials.reconstruct_injective e he
    simpa only [map_zero] using hz
  · exact (FiniteMonomials.mem_range_iff e he _).mp ⟨c,rfl⟩
  · intro n
    have hz := congrFun hzero n
    change SecondJetRank.contactMap (K := K) m
      (coefficientLocal e m (x n) (u0 n) (u1 n) c) = 0 at hz
    have hd : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (coefficientLocal e m (x n) (u0 n) (u1 n) c) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    exact untruncate_contact (SecondJetLocal.contact (K := K)).toRingHom Polynomial.X m _
      SecondJetLocal.contact_X hd

end Interpolant
end
end ProximityPrize.SubmissionLower.Koala6831Residual

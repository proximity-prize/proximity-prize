import ProximityPrize.SubmissionLower.Koala6844VirtualHighOrdinaryContacts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false

variable {K J : Type} [Field K]

def allSourceContacts (C : J → LocalContact K) (D w y b c : ℕ) :
    globalBox K D w y b c →ₗ[K] (∀ i : J, (C i).target y b c) :=
  LinearMap.pi (fun i => sourceContact (C i).center D w y b c
    (C i).length (C i).multiplicity (C i).relation)

theorem mem_ideal_of_mem_contactKernel
    (C : J → LocalContact K) (D w y b c : ℕ)
    (F : globalBox K D w y b c) (h : F ∈ (allSourceContacts C D w y b c).ker) (i : J) :
    MvPolynomial.finSuccEquiv K 3 F.val ∈
      Ideal.span ({((Polynomial.X : GermCarrier K) -
        Polynomial.C (MvPolynomial.C (C i).center)) ^ (C i).length, (C i).relation} :
        Set (GermCarrier K)) ^ (C i).multiplicity := by
  have hzero := congrFun (LinearMap.mem_ker.mp h) i
  exact mem_local_of_sourceContact_eq_zero
    (C i).center D w y b c (C i).length (C i).multiplicity (C i).relation F hzero

theorem finrank_pi_ker_add_budget {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Fintype J] {W : J → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)] [∀ i, Module.Free K (W i)] (maps : ∀ i, V →ₗ[K] W i) :
    Module.finrank K V ≤ Module.finrank K (LinearMap.pi maps).ker +
      ∑ i : J, Module.finrank K (W i) := by
  let f : V →ₗ[K] (∀ i, W i) := LinearMap.pi maps
  have h := f.finrank_range_add_finrank_ker
  have hr : Module.finrank K f.range ≤ Module.finrank K (∀ i, W i) := Submodule.finrank_le f.range
  rw [Module.finrank_pi_fintype] at hr
  change _ ≤ Module.finrank K f.ker + _
  omega

theorem finrank_contactKernel_add_budget [Fintype J]
    (C : J → LocalContact K) (D w y b c : ℕ) :
    Module.finrank K (globalBox K D w y b c) ≤
      Module.finrank K (allSourceContacts C D w y b c).ker +
        ∑ i : J, Module.finrank K ((C i).target y b c) := by
  letI (i : J) : Module.Finite K ((C i).target y b c) := by
    unfold LocalContact.target
    exact Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  letI (i : J) : Module.Free K ((C i).target y b c) := by
    unfold LocalContact.target
    exact Module.Free.of_divisionRing K _
  let maps (i : J) : globalBox K D w y b c →ₗ[K] (C i).target y b c :=
    sourceContact (C i).center D w y b c (C i).length (C i).multiplicity (C i).relation
  have h := finrank_pi_ker_add_budget (K := K) (V := globalBox K D w y b c)
    (W := fun i => (C i).target y b c) maps
  exact h

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

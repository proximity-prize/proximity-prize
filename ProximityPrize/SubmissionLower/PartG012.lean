import ProximityPrize.SubmissionLower.PartG011


section Compact_TriangularKernel
/-! Linear algebra for checking a kernel family one initial component at a
time. This is intended for the second-jet construction, whose lowest epsilon
coefficient has an injective diagonal map. -/
namespace ProximityPrize.SubmissionLower.TriangularKernel
noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K] {n : ℕ}
variable {V W : Fin n → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

theorem eq_zero_of_triangular
    (F : (∀ i, V i) →ₗ[K] (∀ i, W i))
    (D : ∀ i, V i →ₗ[K] W i)
    (hD : ∀ i, Function.Injective (D i))
    (hdiag : ∀ v i, (∀ j, j.val < i.val → v j = 0) →
      F v i = D i (v i))
    (v : ∀ i, V i) (hv : F v = 0) : v = 0 := by
  have hall : ∀ k : ℕ, ∀ i : Fin n, i.val = k → v i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      apply hD i
      calc
        D i (v i) = F v i := (hdiag v i (fun j hj =>
          ih j.val (by omega) j rfl)).symm
        _ = 0 := congrFun hv i
        _ = D i 0 := (map_zero (D i)).symm
  funext i
  exact hall i.val i rfl

theorem injective_of_triangular
    (F : (∀ i, V i) →ₗ[K] (∀ i, W i))
    (D : ∀ i, V i →ₗ[K] W i)
    (hD : ∀ i, Function.Injective (D i))
    (hdiag : ∀ v i, (∀ j, j.val < i.val → v j = 0) →
      F v i = D i (v i)) : Function.Injective F := by
  intro v u h
  apply sub_eq_zero.mp
  apply eq_zero_of_triangular F D hD hdiag (v-u)
  rw [map_sub, h, sub_self]

end
end ProximityPrize.SubmissionLower.TriangularKernel

end Compact_TriangularKernel

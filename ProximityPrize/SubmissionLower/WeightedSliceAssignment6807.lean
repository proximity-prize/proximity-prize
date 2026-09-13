import ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807
/-
UNCOMPILED. Choose one actual factor/component for each embedded point.
This supplies a disjoint weighted partition, including points lying on more
than one component, rather than counting an overlapping cover as a partition.
-/
import ProximityPrize.SubmissionLower.PureFlagSliceBudget6807

namespace ProximityPrize.SubmissionLower.WeightedSliceAssignment6807
open scoped Classical BigOperators
open RCN002 RCN007 RCN072 RCN084 RCN095 RCN134 RCN264
noncomputable section
set_option autoImplicit false
local instance {A : Type*} : DecidableEq A := Classical.decEq A
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {E I : Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" => MvPolynomial (Fin 3) E

abbrev SliceComponent (F N R : Poly) :=
  (g : ↥(activeFactors F N)) × RegularComponent E g.1 N R

theorem exists_point_assignment (F N R : Poly) (point : I → Fin 3 → E)
    (hcover : ∀ i, ∃ g : ↥(activeFactors F N), MvPolynomial.eval (point i) g.1 = 0)
    (hN : ∀ i, MvPolynomial.eval (point i) N = 0)
    (hR : ∀ i, MvPolynomial.eval (point i) R ≠ 0) :
    ∃ assign : I → SliceComponent F N R,
      ∀ i, (assign i).2.1 ≤ RingHom.ker
        (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom := by
  classical
  have he (i : I) : ∃ a : SliceComponent F N R,
      a.2.1 ≤ RingHom.ker (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom := by
    obtain ⟨g, hg⟩ := hcover i
    obtain ⟨C, hC⟩ := exists_regular_component E g.1 N R (point i) hg (hN i) (hR i)
    exact ⟨⟨g,C⟩,hC⟩
  exact ⟨fun i => (he i).choose, fun i => (he i).choose_spec⟩

omit [Field E] [IsAlgClosed E] in
/-- Exact weighted regrouping, valid for any finite target type. -/
theorem weighted_assignment_sum {A : Type*} [Fintype A] [DecidableEq A]
    (assign : I → A) (mu : I → ℕ) :
    (∑ a, ∑ i with assign i = a, mu i) = ∑ i, mu i := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := assign) (fun _ _ => Finset.mem_univ _) _

omit [Field E] [IsAlgClosed E] in
/-- Local bounds can be summed without multiplying a point's weight by the
number of components through it. The local hypothesis is still visible. -/
theorem sum_local_slice_bounds {A : Type*} [Fintype A] [DecidableEq A]
    (assign : I → A) (mu : I → ℕ) (cost : A → ℕ) (d : ℕ)
    (hlocal : ∀ a, d * (∑ i with assign i = a, mu i) ≤ cost a) :
    d * (∑ i, mu i) ≤ ∑ a, cost a := by
  rw [← weighted_assignment_sum assign mu, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hlocal a)

/-- The old first-tail polynomial is nonzero on every assigned slice component
through an embedding point, by the k=0 isolation certificate. -/
theorem first_tail_not_mem_assigned (F N A R : Poly)
    (point : I → Fin 3 → E) (assign : I → SliceComponent F N R)
    (hpoint : ∀ i, (assign i).2.1 ≤ RingHom.ker
      (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom)
    (hisolated : ∀ i, IsolatedPoint F N A (point i)) (i : I) :
    A ∉ (assign i).2.1 := by
  let g := (assign i).1
  let C := (assign i).2
  exact hisolated i C.1 inferInstance (regularComponent_ne_point E g.1 N R C)
    (hpoint i)
    (C.1.mem_of_dvd (activeFactors_spec F N g).2.1
      (regularComponent_G_mem E g.1 N R C))
    (regularComponent_T_mem E g.1 N R C)

end
end ProximityPrize.SubmissionLower.WeightedSliceAssignment6807

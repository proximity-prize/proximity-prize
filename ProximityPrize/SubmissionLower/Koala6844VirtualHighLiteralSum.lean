import ProximityPrize.SubmissionLower.Koala6844VirtualHighPoleSum
import ProximityPrize.SubmissionLower.Koala6844VirtualHighFiniteProjection
import ProximityPrize.SubmissionLower.Koala6831IntrinsicLongLiteral


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN001 RCN002 RCN007 RCN009 RCN013 RCN093 RCN112 RCN120 RCN264
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option linter.style.haveILetI false

variable {Ω A : Type} [Field Ω] [IsAlgClosed Ω] [Fintype A]
variable {G T H : MvPolynomial (Fin 3) Ω}

theorem sum_weighted_literal_degree_le
    (component : A → RegularComponent Ω G T H) (hinj : Function.Injective component)
    (μ : A → ℕ) (positive : ∀ a, 1 ≤ μ a)
    (primary : ∀ a, ∃ s ∉ (component a).1,
      s * T ∈ Ideal.span {G} ⊔ (component a).1 ^ μ a)
    (hG : Irreducible G) (hproper : ¬ G ∣ T) (i : Fin 3) :
    (∑ a, μ a * actualCoordinateDegree Ω (component a).1 i) ≤
      RCN001.coordinateMixedDegree Ω G T i := by
  classical
  let Active := {a : A // Transcendental Ω (coordinate Ω (component a).1 i)}
  let component' (a : Active) := component a.1
  let f (a : A) := μ a * actualCoordinateDegree Ω (component a).1 i
  have sumActive : (∑ a, f a) = ∑ a : Active, f a.1 := by
    calc
      _ = ∑ a ∈ Finset.univ.filter (fun a => Transcendental Ω (coordinate Ω (component a).1 i)), f a := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hn
        have halgebraic : ¬ Transcendental Ω (coordinate Ω (component a).1 i) :=
          fun ht => hn (Finset.mem_filter.mpr ⟨ha, ht⟩)
        simp only [f, actualCoordinateDegree, dite_eq_right halgebraic, mul_zero]
      _ = _ := by
        simpa only [Active, Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset A)) f
            (p := fun a => Transcendental Ω (coordinate Ω (component a).1 i))).symm
  change (∑ a, f a) ≤ _
  rw [sumActive]
  by_cases hA : Nonempty Active
  · obtain ⟨a₀⟩ := hA
    let order := Equiv.swap (0 : Fin 3) i
    have orderBase : order 0 = i := Equiv.swap_apply_left 0 i
    have hAt : Transcendental Ω (coordinate Ω (component' a₀).1 (order 0)) := by
      simpa only [orderBase] using a₀.2
    obtain ⟨order', position, same, outer⟩ :=
      exists_positive_outer_order Ω order (component' a₀).1 G hG
        (regularComponent_G_mem Ω G T H (component' a₀)) hAt
    have sameI : order' 0 = i := same.trans orderBase
    have hActual (a : Active) : Transcendental Ω (coordinate Ω (component' a).1 (order' 0)) := by
      simpa only [sameI] using a.2
    have hProjected (a : Active) : Transcendental Ω
        (flagEvaluation Ω (component' a).1 0 0 0 (MvPolynomial.X (order' 0))) := by
      simpa only [flagEvaluation_zero_X] using hActual a
    have finiteField (a : Active) :
        letI := flagBaseAlgebra Ω (component' a).1 0 0 0 order' (hProjected a)
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (component' a).1) := by
      rw [flagBaseAlgebra_zero_eq _ _ (hProjected a) (hActual a)]
      exact finite_literal_projection Ω order' (component' a).1 (hActual a) G T hG
        (regularComponent_G_mem Ω G T H (component' a))
        (regularComponent_T_mem Ω G T H (component' a)) hproper
    have degrees (a : Active) :
        projectedFiniteDegree component' 0 0 0 order' hProjected a =
          actualCoordinateDegree Ω (component' a).1 i := by
      have equal :
          projectedFiniteDegree component' 0 0 0 order' hProjected a =
            actualCoordinateDegree Ω (component' a).1 (order' 0) := by
        rw [actualCoordinateDegree_of_transcendental _ _ _ (hActual a)]
        unfold projectedFiniteDegree
        rw [flagBaseAlgebra_zero_eq _ _ (hProjected a) (hActual a)]
      exact equal.trans (congrArg (actualCoordinateDegree Ω (component' a).1) sameI)
    have cap : originalMixedDegree Ω order' G T = RCN001.coordinateMixedDegree Ω G T i := by
      change originalMixedDegree Ω order' G T = originalMixedDegree Ω order G T
      rcases position with h | h
      · rw [h]
      · rw [h, originalMixedDegree_swap]
    have res : (flagPlaneResultant (0 : Ω) 0 0 order' G T).natDegree ≤
        RCN001.coordinateMixedDegree Ω G T i := by
      rw [flagPlaneResultant_zero_eq, ← cap]
      exact planeMap_resultant_natDegree_le Ω order' G T
    have summed := sum_weighted_projection_degree_le component' 0 0 0 order' hProjected
      finiteField (fun a => zero_flag_generators (component' a).1 order' (hProjected a))
      (fun a => μ a.1) (fun a => positive a.1) (fun a => primary a.1)
      (hinj.comp Subtype.val_injective) hG hproper
      (by simpa only [flagPlaneMap_zero_apply] using outer) _ res
    simpa only [degrees, f, component'] using summed
  · letI : IsEmpty Active := not_nonempty_iff.mp hA
    simp

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh


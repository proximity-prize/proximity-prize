import ProximityPrize.SubmissionLower.WeightedSliceAssignment6807
import ProximityPrize.SubmissionLower.PureFlagSliceBudget6807
namespace ProximityPrize.SubmissionLower.SmallSliceBudgets6807
open scoped Classical BigOperators
open RCN095 RCN237 RCN264 RCN340 RCN341 RCN084 RCN039 RCN046
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
variable {E : Type} [Field E] [IsAlgClosed E]
local notation "Poly" => MvPolynomial (Fin 3) E

structure SliceBudgets (F N R : Poly) (q : FlagDegree) where
  base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent E g.1 N R,
    SeparableLiteralCoordinate C.1
  unit : ∀ g : ↥(activeFactors F N),
    AdaptiveUnitPoleBudget (base g) (exactFlag g.1) q

theorem exists_sliceBudgets (F N R : Poly) (p q : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F) (hNq : PolynomialInFlag q N)
    (c : ℕ) [CharP E c] (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c) :
    Nonempty (SliceBudgets F N R q) := by
  classical
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data F N R hF p q hFp hNq
    c hdeg hmix
  have he (g : ↥(activeFactors F N)) :
      Nonempty (AdaptiveUnitProjectionFamily (base g) (exactFlag g.1) q) := by
    have hg := activeFactors_spec F N g
    exact exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
      ((support_subset_flagSupport_iff _ _).mpr hNq)
  exact ⟨⟨base, fun g => (Classical.choice (he g)).toAdaptiveUnitPoleBudget⟩⟩

theorem sum_cost_le (F N R : Poly) (p q r : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F) (B : SliceBudgets F N R q) :
    (∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
      (B.unit g).toPrimeFlagBudgetFamily.weightedCost r C) ≤ flagMixed p q r :=
  PureFlagSliceBudget6807.all_active_slice_costs_le F N R hF p q r hFp B.base B.unit

end
end ProximityPrize.SubmissionLower.SmallSliceBudgets6807

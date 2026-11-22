import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3_4
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators
def graphCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) +
    (Polynomial.X (R := Equation)) * C (liftEquation g.derivative)
structure ThresholdPair (i : Fin 4) (P Q : Jet) (r : ℕ) where
  left : Jet
  right : Jet
  proper : ProperPair left right
  left_caps : RowCaps left (cheapShape i)
  right_caps : RowCaps right (layeredShape i)
  heavy : Finset Equation
  factors : ∀ f ∈ heavy, Irreducible f ∧ 0 < f.natDegree ∧ f.natDegree < p ∧
    C f ∣ P ∧ C f ∣ Q
  seed_budget : (∑ f ∈ heavy, (ordinarySeedDegree f : ℚ)) ≤ (cheapShape i).U / (r : ℚ)
  y_budget : (∑ f ∈ heavy, (f.natDegree : ℚ)) ≤ (cheapShape i).B / (r : ℚ)
  residual_order : ∀ q : Surface, Parent q →
    OrderAt q P (reserve i + 1) → OrderAt q Q (reserve i + 1) →
    (∀ f ∈ heavy, C f ∉ q.asIdeal) →
    OrderAt q left (reserve i + 2 - r) ∧ OrderAt q right (reserve i + 2 - r)
end
end K1_14_3_4
end

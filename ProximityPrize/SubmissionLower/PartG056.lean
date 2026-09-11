import ProximityPrize.SubmissionLower.PartG055


section Compact_SecondJetRetainedBudgets
/-! The weighted moving-degree estimate on the actual first-tail components,
assuming the proper derivative-helper alternatives have been excluded. -/
namespace ProximityPrize.SubmissionLower.SecondJetRetainedBudgets
open scoped Classical BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

theorem exists_retained_budgets (φ : Polynomial K →+* E)
    (F : MvPolynomial (Fin 4) K) (carrier A : MvPolynomial (Fin 3) E)
    (hcarrier : carrier ∣ surfaceMap φ F)
    (P : Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (base : ∀ C : RegularComponent E carrier A (surfaceMap φ (RCN313.polyH K F)),
      SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q) :
    ∃ budget : ∀ C : RegularComponent E carrier A (surfaceMap φ (RCN313.polyH K F)),
      MovingPoleBudget C.1 (surfaceMap φ (RCN313.polyH K F)) (surfaceMap φ (RCN313.polyG K F)),
      (∀ C, (budget C).zCost = coordinateDegree E (CoordinateField E C.1) (unit.zProjection C) ∧
        (budget C).yzCost = coordinateDegree E (CoordinateField E C.1) (unit.yzProjection C) ∧
        (budget C).allCost = coordinateDegree E (CoordinateField E C.1) (unit.allProjection C)) ∧
      (k+1)*(∑ C ∈ Finset.univ.filter (fun C : RegularComponent E carrier A
          (surfaceMap φ (RCN313.polyH K F)) => surfaceMap φ (asS P).leadingCoeff ∉ C.1),
        (budget C).movingCost) ≤ flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
  classical
  let H := surfaceMap φ (RCN313.polyH K F)
  let G := surfaceMap φ (RCN313.polyG K F)
  let active := Finset.univ.filter (fun C : RegularComponent E carrier A H =>
    surfaceMap φ (asS P).leadingCoeff ∉ C.1)
  have hlead : ∀ C ∈ active, surfaceMap φ (asS P).leadingCoeff ∉ C.1 :=
    fun C hC => (Finset.mem_filter.mp hC).2
  have hF : ∀ C : RegularComponent E carrier A H, surfaceMap φ F ∈ C.1 := by
    intro C
    obtain ⟨Q,hQ⟩ := hcarrier
    rw [hQ]
    exact C.1.mul_mem_right _ (regularComponent_G_mem E carrier A H C)
  apply SecondJetActiveMovingBudget.exists_budgets carrier A H G base p q unit
    (MvPolynomial.map (φ.comp Polynomial.C) P) (φ Polynomial.X) B U L (k+1) n0
    hBU hUL hdn hB (SecondJetSurfaceMap.mapped_support_bounds _ P B U L hP) active
    (fun C => SecondJetComponentRoots.componentPolynomial φ C.1 P)
    (fun C j => SecondJetComponentRoots.coefficients φ C.1 P j)
    (fun C hC => (SecondJetComponentRoots.degree_retained φ C.1 P (hlead C hC)).1)
    (fun C hC => ?_) (fun C hC => ?_) h2
  · rw [(SecondJetComponentRoots.degree_retained φ C.1 P (hlead C hC)).2]
    exact hn
  · exact SecondJetComponentRoots.roots_retained φ C.1 P F s k hS (hF C)
      (regularComponent_H_not_mem E carrier A H C) (hlead C hC) hdiv h2 hfact

end
end ProximityPrize.SubmissionLower.SecondJetRetainedBudgets

end Compact_SecondJetRetainedBudgets

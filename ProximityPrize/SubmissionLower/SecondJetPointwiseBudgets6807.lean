import ProximityPrize.SubmissionLower.ReducedCommonLinear6807
/-
UNCOMPILED SOURCE EXTRACTION. No new geometric assertion is postulated.
The frozen proof already establishes hpoint; this file returns it instead
of discarding it. The entire hpoint block is preserved byte-for-byte.
See pointwise_extraction_audit.json. A real Lean build is still required.
-/
import ProximityPrize.SubmissionLower.LowerGeometry

section Compact_SecondJetActiveMovingBudget6807
/-! Moving budgets for the retained components, using their actual integer
projection degrees and the second-jet weighted root bound. -/
namespace ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget6807
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (SeparableCoordinate coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K : Type} [Field K] [IsAlgClosed K]

theorem exists_budgets (F A H G : MvPolynomial (Fin 3) K)
    (base : ∀ C : RegularComponent K F A H, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (P : SecondJetSupport.Poly (K := K)) (freezeX : K) (B U T d n0 : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : d ≤ n0) (hB : 2*(n0-d) ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (active : Finset (RegularComponent K F A H))
    (Q : ∀ C : RegularComponent K F A H, Polynomial (CoordinateField K C.1))
    (hQcoeff : ∀ (C : RegularComponent K F A H) (j : ℕ),
      (Q C).coeff j = MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K C.1))
        (coordinate K C.1)
        (SecondJetFlagCoefficients.freeze freezeX ((SecondJetCoefficients.asS P).coeff j)))
    (hQ : ∀ C ∈ active, Q C ≠ 0)
    (hn : ∀ C ∈ active, n0 ≤ (Q C).natDegree)
    (hroot : ∀ C ∈ active,
      (Polynomial.X-Polynomial.C (RCN064.movingRatio C.1 H G/2))^d ∣ Q C)
    (h2 : (2 : K) ≠ 0) :
    ∃ budget : ∀ C : RegularComponent K F A H, MovingPoleBudget C.1 H G,
      (∀ C, (budget C).zCost = coordinateDegree K (CoordinateField K C.1) (unit.zProjection C) ∧
        (budget C).yzCost = coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C) ∧
        (budget C).allCost = coordinateDegree K (CoordinateField K C.1) (unit.allProjection C)) ∧
      (∀ C ∈ active, d*(budget C).movingCost ≤
        unit.toPrimeFlagBudgetFamily.weightedCost
          (SecondJetRelaxedFlag.budgetFlag B U T d n0) C) ∧
      d*(∑ C ∈ active, (budget C).movingCost) ≤
        flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T d n0) := by
  classical
  obtain ⟨Q0,U0,J,hQ0,hU0,hJ⟩ := RCN209.exists_separable_moving_coordinates F A H G base
  let budget : ∀ C : RegularComponent K F A H, MovingPoleBudget C.1 H G :=
    RCN200.budgetOfProjections F A H G unit J (fun C v => (hJ C).2.2.1 v)
  let flag := SecondJetRelaxedFlag.budgetFlag B U T d n0
  have hpoint : ∀ C ∈ active, d*(budget C).movingCost ≤
      unit.toPrimeFlagBudgetFamily.weightedCost flag C := by
    intro C hC
    let D := base C
    letI := polynomialBaseAlgebra K C.1 D.index
    letI := rationalBaseAlgebra K C.1 D.index D.transcendental
    letI := polynomialBaseScalarTower K C.1 D.index
    letI := polynomialRationalScalarTower K C.1 D.index D.transcendental
    letI := rationalBaseScalarTower K C.1 D.index D.transcendental
    letI : FiniteDimensional (RatFunc K) (CoordinateField K C.1) := D.finite
    letI : Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1) := D.separable
    have hpole : ∀ v : RCN026.Place K (CoordinateField K C.1),
        poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C)) =
        max (2*flagPole v.val (coordinate K C.1) unitAllFlag)
          (flagPole v.val (coordinate K C.1) unitYZFlag+
            poleOrder v.val (RCN064.movingRatio C.1 H G/2)) := by
      intro v
      rw [(hJ C).2.2.1 v,SecondJetPoleScaling.pole_half v h2]
      rw [flagPole_unitAll,flagPole_unitYZ]
      rfl
    have hh := SecondJetMovingDegree.degree_bound K (CoordinateField K C.1) P freezeX
      B U T d n0 hBU hUT hdn hB hP (coordinate K C.1) (Q C) (hQcoeff C)
      (hQ C hC) (hn C hC) (RCN064.movingRatio C.1 H G/2) (hroot C hC) (J C)
      hpole ((budget C).weightedCost flag) ((budget C).sum_flagPole_le flag)
    change (d : ℤ)*((budget C).movingCost : ℤ) ≤ ((budget C).weightedCost flag : ℤ) at hh
    have hcost : (budget C).weightedCost flag =
        unit.toPrimeFlagBudgetFamily.weightedCost flag C := rfl
    rw [hcost] at hh
    exact_mod_cast hh
  refine ⟨budget,fun C => ⟨rfl,rfl,rfl⟩,hpoint,?_⟩
  rw [Finset.mul_sum]
  calc
    (∑ C ∈ active, d*(budget C).movingCost) ≤
        ∑ C ∈ active, unit.toPrimeFlagBudgetFamily.weightedCost flag C :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ C, unit.toPrimeFlagBudgetFamily.weightedCost flag C :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ active)
    _ ≤ _ := unit.toPrimeFlagBudgetFamily.sum_weightedCost_le flag

end
end ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget6807

end Compact_SecondJetActiveMovingBudget6807

section Compact_SecondJetRetainedBudgets6807
/-! The weighted moving-degree estimate on the actual first-tail components,
assuming the proper derivative-helper alternatives have been excluded. -/
namespace ProximityPrize.SubmissionLower.SecondJetRetainedBudgets6807
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
      (∀ C : RegularComponent E carrier A (surfaceMap φ (RCN313.polyH K F)),
        surfaceMap φ (asS P).leadingCoeff ∉ C.1 →
        (k+1)*(budget C).movingCost ≤
          unit.toPrimeFlagBudgetFamily.weightedCost
            (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) C) ∧
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
  suffices hh : ∃ budget : ∀ C : RegularComponent E carrier A H,
      MovingPoleBudget C.1 H G,
      (∀ C, (budget C).zCost = coordinateDegree E (CoordinateField E C.1) (unit.zProjection C) ∧
        (budget C).yzCost = coordinateDegree E (CoordinateField E C.1) (unit.yzProjection C) ∧
        (budget C).allCost = coordinateDegree E (CoordinateField E C.1) (unit.allProjection C)) ∧
      (∀ C ∈ active, (k+1)*(budget C).movingCost ≤
        unit.toPrimeFlagBudgetFamily.weightedCost
          (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) C) ∧
      (k+1)*(∑ C ∈ active, (budget C).movingCost) ≤
        flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) by
    obtain ⟨budget,hcost,hpoint,hsum⟩ := hh
    refine ⟨budget,hcost,?_,hsum⟩
    intro C hC
    exact hpoint C (Finset.mem_filter.mpr ⟨Finset.mem_univ C,hC⟩)
  apply SecondJetActiveMovingBudget6807.exists_budgets carrier A H G base p q unit
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
end ProximityPrize.SubmissionLower.SecondJetRetainedBudgets6807

end Compact_SecondJetRetainedBudgets6807

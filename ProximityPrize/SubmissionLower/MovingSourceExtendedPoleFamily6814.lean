import ProximityPrize.SubmissionLower.MovingSourcePairFirstCutPole6814

/-! Actual source-pair moving budgets on the additional field used by
first-cut slices. Ordinary pole costs are preserved and only the moving
sum is replaced by the proved shared pair bound. -/
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedPoleFamily6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 25000
open scoped BigOperators Classical
open RCN002 RCN046 RCN064 RCN095 RCN135 RCN136 RCN199 RCN200 RCN207 RCN209 RCN264 RCN341 RCN344
open MovingFiberThreeSources6811 MovingSourceCoupledClearing6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814
open MovingSourceExtendedPointCount6814 MovingSourceExtendedMovingDegrees6814

variable {K E : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Omega" => E
local notation "Poly3" => MvPolynomial (Fin 3) E

theorem exists_extended_pair_moving_coordinates
    (F : MvPolynomial (Fin 4) K) (SZ : Source F) (G : Poly3) (hGF : G∣frozenCarrier eta F)
    (n : ℕ) (coeff : Fin (n+1) → Poly3)
    (base : ∀ C : ExtendedFactorFamily eta F G n coeff, SeparableLiteralCoordinate C.1)
    (active : Finset (ExtendedFactorFamily eta F G n coeff))
    (hlead : ∀ C∈active, SZ.leading (codeMap eta)∉C.1)
    (scale z u v : ℕ) (W : FlagDegree)
    (hbound : ∀ Q A : Poly3, (2 : Poly3)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget eta F SZ Q A scale z u v)
    (hcut : ∀ Q A : Poly3, PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      PolynomialInFlag W (extendedTargetCut n coeff Q A)) :
    ∃ projection : ∀ C : ExtendedFactorFamily eta F G n coeff, SeparableCoordinate Omega (CoordinateField Omega C.1),
      (∀ (C : ExtendedFactorFamily eta F G n coeff) (nu : RCN026.Place Omega (CoordinateField Omega C.1)),
        RCN187.poleOrder nu.val (SeparableCoordinate.value Omega (CoordinateField Omega C.1) (projection C))=
        movingPoleTarget C.1 (frozenH eta F) (frozenG eta F) nu) ∧
      scale*(∑ C∈active, SeparableCoordinate.degree Omega (CoordinateField Omega C.1) (projection C))≤
        W.zOnly*z+W.yz*u+W.all*v := by
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩ := exists_separable_moving_coordinates
    G (filteredCut n coeff (frozenH eta F) (frozenG eta F)) (frozenH eta F) (frozenG eta F) base
  refine ⟨projection,fun C nu => (hproj C).2.2.1 nu,?_⟩
  by_cases hempty : active=∅
  · simp [hempty]
  obtain ⟨C0,hC0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hAne : A≠0 := by intro hz; exact (hproj C0).1 (hz ▸ C0.1.zero_mem)
  have htwo : (2 : Poly3)≠0 := by
    exact (CharP.cast_eq_zero_iff Poly3 2130706433 2).not.mpr (by decide)
  have hh := sum_extended_moving_degrees eta F SZ G hGF Q A scale z u v
    (hbound Q A (mul_ne_zero htwo hAne) hQ hA) n coeff W (hcut Q A hQ hA)
    (fun C : active => C.val) Subtype.val_injective
    (fun C => hlead C.val C.property) (fun C => (hproj C.val).1)
    (fun C => projection C.val) (fun C => (hproj C.val).2.1)
  rwa [Finset.sum_coe_sort active (fun C =>
    SeparableCoordinate.degree Omega (CoordinateField Omega C.1) (projection C))] at hh

theorem exists_extended_pair_moving_budgets
    (F : MvPolynomial (Fin 4) K) (SZ : Source F) (G : Poly3) (hGF : G∣frozenCarrier eta F)
    (n : ℕ) (coeff : Fin (n+1) → Poly3)
    (base : ∀ C : ExtendedFactorFamily eta F G n coeff, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (active : Finset (ExtendedFactorFamily eta F G n coeff))
    (hlead : ∀ C∈active, SZ.leading (codeMap eta)∉C.1)
    (scale z u v : ℕ) (W : FlagDegree)
    (hbound : ∀ Q A : Poly3, (2 : Poly3)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget eta F SZ Q A scale z u v)
    (hcut : ∀ Q A : Poly3, PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      PolynomialInFlag W (extendedTargetCut n coeff Q A)) :
    ∃ budget : ∀ C : ExtendedFactorFamily eta F G n coeff, MovingPoleBudget C.1 (frozenH eta F) (frozenG eta F),
      (∀ C, (budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C) ∧
      scale*(∑ C∈active, (budget C).movingCost)≤W.zOnly*z+W.yz*u+W.all*v := by
  obtain ⟨projection,hpole,hsum⟩ := exists_extended_pair_moving_coordinates eta F SZ G hGF n coeff base active hlead
    scale z u v W hbound hcut
  refine ⟨budgetOfProjections G (filteredCut n coeff (frozenH eta F) (frozenG eta F)) (frozenH eta F) (frozenG eta F)
    unit projection hpole,fun C => ⟨rfl,rfl,rfl⟩,hsum⟩

/-- Every geometric and degree-budget input on the new side is supplied
from actual coprime Sources. Only the ordinary Stage frame and its actual
coefficient cut remain caller inputs. -/
theorem exists_extended_source_moving_budgets
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (parent : FlagDegree) (hp : PolynomialInFlag parent (extendedCarrier eta F))
    (hunit : 2*(parent.zOnly+parent.yz+parent.all)<2130706433)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433)
    (G : Poly3) (hGF : G∣frozenCarrier eta F) (n : ℕ) (coeff : Fin (n+1) → Poly3)
    (base : ∀ C : ExtendedFactorFamily eta F G n coeff, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (active : Finset (ExtendedFactorFamily eta F G n coeff))
    (hlead : ∀ C∈active, SZ.leading (codeMap eta)∉C.1)
    (W : FlagDegree)
    (hcut : ∀ Q A : Poly3, PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      PolynomialInFlag W (extendedTargetCut n coeff Q A)) :
    ∃ budget : ∀ C : ExtendedFactorFamily eta F G n coeff, MovingPoleBudget C.1 (frozenH eta F) (frozenG eta F),
      (∀ C, (budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (SZ.d*d)*(∑ C∈active, (budget C).movingCost)≤
        W.zOnly*(d*flagMixed parent unitZFlag SZ.flag)+
        W.yz*(SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag)+
        W.all*(SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  exact exists_extended_pair_moving_budgets eta F SZ G hGF n coeff base p q unit active hlead _ _ _ _ W
    (fun Q A hden hQ hA => extended_sources_point_budget eta F hF hpos hsmall S T hcop d hd hS hT hchar
      SZ hZchar parent hp hunit Q A hden hQ hA hz hu) hcut


#print axioms exists_extended_pair_moving_budgets
#print axioms exists_extended_source_moving_budgets
end
end ProximityPrize.SubmissionLower.MovingSourceExtendedPoleFamily6814

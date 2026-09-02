/-
C2 FOUNDATION: transporting the unit family across a congruent cut, and the
moving-budget existence at an ARBITRARY first-tail flag.

C2 replaces the sharp first tail `sharpResidualAgreementFlag (support a b s) (w+1)`
by the reduced one `reducedResidualAgreementFlag (support a b s) (w+1)`, which is
strictly `Below` it (same `yz + all` and total, `all` smaller by `w + 1`).  The
reduced geometry lives over the components of `reducedFirstCut`, so it has to be
transported to the components of `globalTailCut (w+1)`.

`PrimeFlagBudgetFamily.ofCongruentCut` (B1.lean:108) already transports the
budget family, and `RCN335` uses it for the certificate.  What is missing for the
hybrid moving route is the transport of the whole `AdaptiveUnitProjectionFamily`,
because `exists_moving_pole_budget_family` needs the projections themselves in
order to produce a `MovingPoleBudget` whose costs agree with the family's.

§1 supplies that transport.  Every field of `AdaptiveUnitProjectionFamily`
mentions the component only through `C.1`, and `regularComponentEquiv h C` has
`.1 = C.1` definitionally, so the transport is a precomposition.

§2 generalises `RCN085.exists_firstTail_cut_budgets` (J3.lean:13) in the
first-tail flag.  J3 hard-codes the sharp flag purely to state the three
`z / yz / all` sum bounds through `mixed_sharp_le_padded`; the hybrid route uses
only the cost equalities and the moving sum, both of which are flag-agnostic.
-/
import ProximityPrize.SubmissionLower.J3
import ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1

namespace ProximityPrize.SubmissionLower.LocatorHybridTransportC2
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086 RCN085
open RCN066 RCN135 RCN159 RCN074 RCN237 RCN244 RCN327 RCN263 RCN206 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

/-! ### 1. Transport of a unit family across a congruent cut -/

section Transport
variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
  {G T T' H : MvPolynomial (Fin 3) Omega}

/-- An `AdaptiveUnitProjectionFamily` over the components of `T'` transports to
the components of `T` whenever `G ∣ T - T'`, for any choice of `base`.  All the
structure's fields see the component only through `C.1`, and the equivalence
preserves `C.1` definitionally. -/
def unitFamilyOfCongruentCut (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1) :
    AdaptiveUnitProjectionFamily base p q where
  zProjection C := U.zProjection (regularComponentEquiv h C)
  yzProjection C := U.yzProjection (regularComponentEquiv h C)
  allProjection C := U.allProjection (regularComponentEquiv h C)
  zValue C := U.zValue (regularComponentEquiv h C)
  allTranscendental C := U.allTranscendental (regularComponentEquiv h C)
  zPole_eq C := U.zPole_eq (regularComponentEquiv h C)
  yzPole_eq C := U.yzPole_eq (regularComponentEquiv h C)
  allPole_eq C := U.allPole_eq (regularComponentEquiv h C)
  sum_zDegree_le := by
    refine Eq.trans_le ?_ U.sum_zDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_yzDegree_le := by
    refine Eq.trans_le ?_ U.sum_yzDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_allDegree_le := by
    refine Eq.trans_le ?_ U.sum_allDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)

/-- The transported unit family carries exactly the costs of the transported
budget family, so the hybrid provider can use the two interchangeably. -/
theorem unitFamilyOfCongruentCut_costs (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1)
    (C : RegularComponent Omega G T H) :
    (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.zCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).zCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.yzCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).yzCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.allCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).allCost C := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end Transport

/-! ### 2. Moving budgets at an arbitrary first-tail flag -/

section Budgets
variable {K Ω E : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
  [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E]

/-- `RCN085.exists_firstTail_cut_budgets` with the first-tail flag left free.
Only the cost equalities and the moving sum are produced; the three `z / yz /
all` sum bounds of J3 are exactly the parts that needed the sharp flag, and the
hybrid route never uses them. -/
theorem exists_firstTail_moving_budgets
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Ω) (a b s w : ℕ) (hw : 1 ≤ w)
    (hT : T = globalTailCut φ F (w + 1))
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap φ F) (hGflag : PolynomialInFlag flag G)
    (base : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      SeparableLiteralCoordinate C.1)
    (tailFlag : FlagDegree)
    (unit : AdaptiveUnitProjectionFamily base flag tailFlag)
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
      (∀ C, (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (RCN206.fiberFlag a b s)
        (center a b s + (w + 1) • RCN206.surfaceFlag a b s) := by
  classical
  obtain ⟨coeffs, cflags, heq, hcoeff, hclass⟩ := globalTailCut_certificate
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
  obtain ⟨hHflag, hGcontact⟩ := surfaceMap_HG_flags
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
  have hderiv : regularitySurface φ F ∈
      Ideal.span ({G, MvPolynomial.pderiv (1 : Fin 3) G} :
        Set (MvPolynomial (Fin 3) Ω)) := by
    rw [regularitySurface, ← RCN267.surfaceMap_pderiv_R]
    exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
  have hT' : T = filteredCut w coeffs (surfaceMap φ (polyH K F))
      (surfaceMap φ (polyG K F)) := hT.trans heq
  clear hT
  subst T
  obtain ⟨budget, hcost, hz, hyz, ha, hm⟩ :=
    exists_moving_pole_budget_family (E := E)
      G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
      base flag tailFlag unit hG hderiv hGflag
      a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
      (by convert hmix using 1 <;> ring)
  refine ⟨budget, hcost, hm.trans ?_⟩
  rw [mixed_affine_third, mixed_affine_third]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _

end Budgets

end
end ProximityPrize.SubmissionLower.LocatorHybridTransportC2

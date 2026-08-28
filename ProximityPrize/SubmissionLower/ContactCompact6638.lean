import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research
import ProximityPrize.SubmissionLower.ContactFlagGeneralPrincipalCyclesResearch
import ProximityPrize.SubmissionLower.ContactFlagProjectionPositivity6543Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactAdaptiveUnitPoleFamilyResearch
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research
import ProximityPrize.SubmissionLower.ContactSingularBranch6600Research
import ProximityPrize.SubmissionLower.ContactSharpFactorAggregationPost6600Research
import ProximityPrize.SubmissionLower.ContactTetraGeometricSeedCover6622Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research
import ProximityPrize.SubmissionLower.AlignmentProtocol6600ConditionalResearch
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
import ProximityPrize.SubmissionLower.ContactParameters6600Research

/-!
# Compact score-66.38 proof assembly

This module preserves the declarations and namespaces of the fifteen terminal
adapter modules while placing them in one compilation unit. Their declarations
appear in prerequisite-first order; only prerequisites outside this compact
unit are imported.
-/


/-!
# Adaptive nested projections as the shared score-66 unit family

This file packages the component-adaptive literal/affine coordinates selected
by `exists_adaptiveNestedProjectionData` into the exact three shared unit
projection budgets.  Algebraic literal or first-affine branches contribute
degree zero; the trapezoid resultant is applied only to their transcendental
subfamilies.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research

open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField ActualCurveRationalProjection
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveProjectionCoordinateResearch
open ContactAdaptiveUnitPoleFamilyResearch
open ContactAdaptiveNestedProjection6600Research
open ContactFlagBezout6543Research ContactFlagPoleInequality6543Research
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagTrapezoidCaps6543Research
open ContactFlagSymbolicTrapezoidResearch
open ContactFlagProjectionPositivity6543Research
open ContactFlagPrincipalCycles6543Research
open ContactFlagTriangularProjectionResearch
open ArbitraryRationalProjectionResearch

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- The common adaptive nested projection gives the three exact unit-support
coordinate families and their sharp symbolic trapezoid degree sums. -/
def adaptiveUnitProjectionFamily_of_nested
    (p q : FlagDegree)
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (hZ : ∀ C : RegularComponent Omega G T H,
      LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (D : AdaptiveNestedProjectionData base hZ hSderiv)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p)
    (hTsupport : T.support ⊆ flagSupport q) :
    AdaptiveUnitProjectionFamily base p q := by
  classical
  let lam := D.lam
  let mu := D.mu
  let nu := D.mu * D.lam
  let zProj : ∀ C : RegularComponent Omega G T H,
      Coordinate Omega (CoordinateField Omega C.1) := fun C =>
    coordinateOfGate (coordinate Omega C.1 2) (hZ C)
  let uProj : ∀ C : RegularComponent Omega G T H,
      Coordinate Omega (CoordinateField Omega C.1) := fun C =>
    coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
  let vProj : ∀ C : RegularComponent Omega G T H,
      Coordinate Omega (CoordinateField Omega C.1) := fun C => Sum.inr {
    embedding := elementEmbedding Omega (CoordinateField Omega C.1)
      (affineV Omega C.1 D.mu (D.mu * D.lam))
      (D.allAffineTranscendental C)
    finite := D.allFinite C
    separable := D.allSeparable C }
  let gCaps := flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
  let tCaps := flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
  have hTne : T ≠ 0 := by
    intro hzero
    apply hproper
    rw [hzero]
    exact dvd_zero G

  let sZ := {C : RegularComponent Omega G T H //
    Transcendental Omega (coordinate Omega C.1 2)}
  have hinjZ : Function.Injective (fun C : sZ => C.1.1) := by
    intro C E hCE
    apply Subtype.ext
    apply Subtype.ext
    exact hCE
  let htZ : ∀ C : sZ,
      Transcendental Omega
        (flagEvaluation Omega C.1.1 lam mu nu
          (MvPolynomial.X (zOrder 0))) := by
    intro C
    simpa [zOrder, Equiv.swap_apply_def, lam, mu, nu] using C.2
  have hembZ (C : sZ) :
      elementEmbedding Omega (CoordinateField Omega C.1.1)
          (flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (zOrder 0))) (htZ C) =
        elementEmbedding Omega (CoordinateField Omega C.1.1)
          (coordinate Omega C.1.1 2) C.2 :=
    elementEmbedding_congr (htZ C) C.2
      (by simp [zOrder, Equiv.swap_apply_def, lam, mu, nu])
  have hgenZ : ∀ C : sZ,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1.1)
          (flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (zOrder 2)),
          flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (zOrder 1))} :
          Set (CoordinateField Omega C.1.1)) = ⊤ := by
    intro C
    rw [hembZ C]
    simpa [zOrder, Equiv.swap_apply_def, lam, mu, nu] using
      flag_generators_z Omega C.1.1 lam mu nu C.2
  have hfamilyZ := finite_sum_flag_finrank_trapezoid
    (K := Omega) (Q := fun C : sZ => C.1.1) hinjZ lam mu nu zOrder
    htZ hgenZ G T hG
    (fun C => regularComponent_G_mem Omega G T H C.1)
    (fun C => regularComponent_T_mem Omega G T H C.1)
    hproper
    (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
    p.all q.all (p.yz + p.all) (q.yz + q.all)
    (flagMixed p q unitZFlag) hTne
    (by simpa only [gCaps] using gCaps.zOuter)
    (by simpa only [tCaps] using tCaps.zOuter)
    (by simpa only [gCaps] using gCaps.zTotal)
    (by simpa only [tCaps] using tCaps.zTotal)
    (z_flag_trapezoid_budget p q)
  have hsumZ :
      (∑ C : RegularComponent Omega G T H,
        coordinateDegree Omega (CoordinateField Omega C.1) (zProj C)) ≤
        flagMixed p q unitZFlag := by
    have hsplit := sum_coordinateOfGate_degree_eq
      (K := Omega)
      (E := fun C : RegularComponent Omega G T H => CoordinateField Omega C.1)
      (x := fun C => coordinate Omega C.1 2) hZ
    change (∑ C : RegularComponent Omega G T H,
      coordinateDegree Omega (CoordinateField Omega C.1)
        (coordinateOfGate (coordinate Omega C.1 2) (hZ C))) ≤ _
    rw [hsplit]
    calc
      (∑ C : sZ,
        (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
          (elementEmbedding Omega (CoordinateField Omega C.1.1)
            (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
         Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1))) =
          ∑ C : sZ,
            (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
              (elementEmbedding Omega (CoordinateField Omega C.1.1)
                (flagEvaluation Omega C.1.1 lam mu nu
                  (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
             Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)) := by
        apply Finset.sum_congr rfl
        intro C _
        rw [hembZ C]
      _ ≤ _ := hfamilyZ.2

  let sU := {C : RegularComponent Omega G T H //
    Transcendental Omega (affineU Omega C.1 D.lam)}
  have hinjU : Function.Injective (fun C : sU => C.1.1) := by
    intro C E hCE
    apply Subtype.ext
    apply Subtype.ext
    exact hCE
  let htU : ∀ C : sU,
      Transcendental Omega
        (flagEvaluation Omega C.1.1 lam mu nu
          (MvPolynomial.X (uOrder 0))) := by
    intro C
    simpa [uOrder, lam, mu, nu] using C.2
  have hembU (C : sU) :
      elementEmbedding Omega (CoordinateField Omega C.1.1)
          (flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (uOrder 0))) (htU C) =
        elementEmbedding Omega (CoordinateField Omega C.1.1)
          (affineU Omega C.1.1 D.lam) C.2 :=
    elementEmbedding_congr (htU C) C.2
      (by simp [uOrder, lam, mu, nu])
  have hgenU : ∀ C : sU,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1.1)
          (flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (uOrder 2)),
          flagEvaluation Omega C.1.1 lam mu nu
            (MvPolynomial.X (uOrder 1))} :
          Set (CoordinateField Omega C.1.1)) = ⊤ := by
    intro C
    rw [hembU C]
    simpa [uOrder, lam, mu, nu] using
      flag_generators_u Omega C.1.1 lam mu nu C.2
  have hfamilyU := finite_sum_flag_finrank_trapezoid
    (K := Omega) (Q := fun C : sU => C.1.1) hinjU lam mu nu uOrder
    htU hgenU G T hG
    (fun C => regularComponent_G_mem Omega G T H C.1)
    (fun C => regularComponent_T_mem Omega G T H C.1)
    hproper
    (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
    p.all q.all (p.zOnly + p.yz + p.all)
    (q.zOnly + q.yz + q.all) (flagMixed p q unitYZFlag) hTne
    (by simpa only [gCaps] using gCaps.uOuter)
    (by simpa only [tCaps] using tCaps.uOuter)
    (by simpa only [gCaps] using gCaps.uTotal)
    (by simpa only [tCaps] using tCaps.uTotal)
    (u_flag_trapezoid_budget p q)
  have hsumU :
      (∑ C : RegularComponent Omega G T H,
        coordinateDegree Omega (CoordinateField Omega C.1) (uProj C)) ≤
        flagMixed p q unitYZFlag := by
    have hsplit := sum_coordinateOfGate_degree_eq
      (K := Omega)
      (E := fun C : RegularComponent Omega G T H => CoordinateField Omega C.1)
      (x := fun C => affineU Omega C.1 D.lam) D.uGate
    change (∑ C : RegularComponent Omega G T H,
      coordinateDegree Omega (CoordinateField Omega C.1)
        (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C))) ≤ _
    rw [hsplit]
    calc
      (∑ C : sU,
        (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
          (elementEmbedding Omega (CoordinateField Omega C.1.1)
            (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
         Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1))) =
          ∑ C : sU,
            (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
              (elementEmbedding Omega (CoordinateField Omega C.1.1)
                (flagEvaluation Omega C.1.1 lam mu nu
                  (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
             Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)) := by
        apply Finset.sum_congr rfl
        intro C _
        rw [hembU C]
      _ ≤ _ := hfamilyU.2

  let htV : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu
          (MvPolynomial.X (vOrder 0))) := by
    intro C
    simpa [vOrder, Equiv.swap_apply_def, lam, mu, nu] using
      D.allAffineTranscendental C
  have hembV (C : RegularComponent Omega G T H) :
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu
            (MvPolynomial.X (vOrder 0))) (htV C) =
        elementEmbedding Omega (CoordinateField Omega C.1)
          (affineV Omega C.1 D.mu (D.mu * D.lam))
            (D.allAffineTranscendental C) :=
    elementEmbedding_congr (htV C) (D.allAffineTranscendental C)
      (by simp [vOrder, Equiv.swap_apply_def, lam, mu, nu])
  have hgenV : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu
            (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({flagEvaluation Omega C.1 lam mu nu
            (MvPolynomial.X (vOrder 2)),
          flagEvaluation Omega C.1 lam mu nu
            (MvPolynomial.X (vOrder 1))} :
          Set (CoordinateField Omega C.1)) = ⊤ := by
    intro C
    rw [hembV C]
    simpa [vOrder, Equiv.swap_apply_def, lam, mu, nu] using
      flag_generators_v Omega C.1 lam mu nu (D.allAffineTranscendental C)
  have hinjV : Function.Injective
      (fun C : RegularComponent Omega G T H => C.1) := by
    intro C E hCE
    exact Subtype.ext hCE
  have hfamilyV := finite_sum_flag_finrank_trapezoid
    (K := Omega) (Q := fun C : RegularComponent Omega G T H => C.1)
    hinjV lam mu nu vOrder htV hgenV G T hG
    (fun C => regularComponent_G_mem Omega G T H C)
    (fun C => regularComponent_T_mem Omega G T H C)
    hproper
    (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
    (p.yz + p.all) (q.yz + q.all)
    (p.zOnly + p.yz + p.all) (q.zOnly + q.yz + q.all)
    (flagMixed p q unitAllFlag) hTne
    (by simpa only [gCaps] using gCaps.vOuter)
    (by simpa only [tCaps] using tCaps.vOuter)
    (by simpa only [gCaps] using gCaps.vTotal)
    (by simpa only [tCaps] using tCaps.vTotal)
    (v_flag_trapezoid_budget p q)
  have hsumV :
      (∑ C : RegularComponent Omega G T H,
        coordinateDegree Omega (CoordinateField Omega C.1) (vProj C)) ≤
        flagMixed p q unitAllFlag := by
    calc
      _ = ∑ C : RegularComponent Omega G T H,
          (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
            (elementEmbedding Omega (CoordinateField Omega C.1)
              (affineV Omega C.1 D.mu (D.mu * D.lam))
                (D.allAffineTranscendental C)).toRingHom.toAlgebra
           Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)) := by
        apply Finset.sum_congr rfl
        intro C _
        rfl
      _ = ∑ C : RegularComponent Omega G T H,
          (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
            (elementEmbedding Omega (CoordinateField Omega C.1)
              (flagEvaluation Omega C.1 lam mu nu
                (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
           Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)) := by
        apply Finset.sum_congr rfl
        intro C _
        rw [hembV C]
      _ ≤ _ := hfamilyV.2

  have hvValue (C : RegularComponent Omega G T H) :
      coordinateValue Omega (CoordinateField Omega C.1) (vProj C) =
        affineV Omega C.1 D.mu (D.mu * D.lam) := by
    dsimp only [vProj, coordinateValue, SeparableCoordinate.value, Sum.elim_inr]
    exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
      (affineV Omega C.1 D.mu (D.mu * D.lam))
      (D.allAffineTranscendental C)

  refine {
    zProjection := zProj
    yzProjection := uProj
    allProjection := vProj
    zValue := ?_
    allTranscendental := ?_
    zPole_eq := ?_
    yzPole_eq := ?_
    allPole_eq := ?_
    sum_zDegree_le := hsumZ
    sum_yzDegree_le := hsumU
    sum_allDegree_le := hsumV }
  · intro C
    exact coordinateOfGate_value _ _
  · intro C
    rw [hvValue C]
    exact D.allAffineTranscendental C
  · intro C v
    rw [exponentSetPoleWeight_unitZ]
    change _ = ContactLocalPoleBound.poleOrder v.val _
    rw [coordinateOfGate_value]
  · intro C v
    rw [exponentSetPoleWeight_unitYZ]
    change _ = ContactLocalPoleBound.poleOrder v.val _
    rw [coordinateOfGate_value]
    rw [← D.uValue C]
    exact (D.uPole C v).symm
  · intro C v
    rw [exponentSetPoleWeight_unitAll]
    change _ = ContactLocalPoleBound.poleOrder v.val _
    rw [hvValue C, ← D.allValue C]
    exact (D.allPole C v).symm

/-- Fully existential consumer seam: the common finite-avoidance theorem and
the three exact trapezoid calculations together produce the shared budget. -/
theorem exists_adaptiveUnitProjectionFamily_of_nested
    (p q : FlagDegree)
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (hZ : ∀ C : RegularComponent Omega G T H,
      LiteralProjectionGate C 2)
    (hYZ : ∀ C : RegularComponent Omega G T H,
      (KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 0) ≠ 0 ∨
        KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 2) ≠ 0) ∨
      (IsAlgebraic Omega (coordinate Omega C.1 0) ∧
        IsAlgebraic Omega (coordinate Omega C.1 2)))
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p)
    (hTsupport : T.support ⊆ flagSupport q) :
    Nonempty (AdaptiveUnitProjectionFamily base p q) := by
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hZ hYZ hSderiv
  exact ⟨adaptiveUnitProjectionFamily_of_nested p q base hZ hSderiv D
    hG hproper hGsupport hTsupport⟩

end

end ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research


/-!
# Degree-zero-safe recursive component aggregation

At a many-identity terminal state, degree zero need not force the literal
seed coordinate `Z` to be transcendental.  We therefore charge the tail to
`zCost + allCost`.  The adaptive all-coordinate projection is nonconstant
on every non-point regular component, so this charge is always positive;
the extra global mixed-volume term fits inside the score-66 ledger.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research

open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout6543Research
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveTerminalIncidenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactStratifiedResidualComponentAdapter6600Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactNearPencil6600FlagResearch
open ContactIdentityResidualComponentFamily6600Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Full component aggregation with an unconditional all-coordinate fallback
for the degree-zero terminal branch. -/
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ 9)
    (hFys : wt residualYSWeights F ≤ 44)
    (hFtotal : wt residualTotalWeights F ≤ 482)
    (hinj : Set.InjOn x nodes)
    (hdegreeSelected : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ d)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) G = 0)
    (hTpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma d e)
    (hchar : d < p) (hda : d < a)
    (B : PrimeFlagBudgetFamily (G := G) (T := T)
      (H := regularitySurface phi F) surfaceFlag cutFlag)
    (hallPositive : ∀ C : RegularComponent Omega G T
      (regularitySurface phi F), 1 ≤ B.allCost C)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * flagMixed surfaceFlag cutFlag agreementDirection6600 +
        V * flagMixed surfaceFlag cutFlag unitYZFlag +
        (e + 1) * (a - d) *
          (flagMixed surfaceFlag cutFlag unitZFlag +
            flagMixed surfaceFlag cutFlag unitAllFlag) := by
  classical
  let H := regularitySurface phi F
  have hHp : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) H ≠ 0 := by
    intro gamma hgamma
    change MvPolynomial.eval (selectedPoint phi selected gamma)
      (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular gamma hgamma
  let degreeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost agreementDirection6600 C
  let unitCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost unitYZFlag C
  let largeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.zCost C + B.allCost C
  have hcomponent : ∀ C : RegularComponent Omega G T H,
      (componentSeeds Omega G T H Gamma
          (selectedPoint phi selected) C).card * (a - d) ≤
        U * degreeCost C + V * unitCost C +
          (e + 1) * (a - d) * largeCost C := by
    intro C
    let GammaC := componentSeeds Omega G T H Gamma
      (selectedPoint phi selected) C
    let S := regularComponentCurveStage F G T selected Gamma nodes x u0 u1
      p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
      hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    apply recursive_curve_stratified_incidence_of_prime_flag_budget
      hphi S (fun r ↦ B.weightedCost r C) (B.primeBudget C)
      (degreeCost C) (unitCost C) U V (largeCost C)
    · intro t
      simpa only [degreeCost, unitCost] using
        B.weightedCost_residualAgreementFlag C t
    · exact hda
    · intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    · intro D hmany
      have hcard : GammaC.card ≤ e + 1 :=
        D.stage.card_le_pencil_of_many_identities hmany
      have hlargePositive : 1 ≤ largeCost C := by
        exact (hallPositive C).trans (Nat.le_add_left _ _)
      have hscaled : GammaC.card * (a - d) ≤ (e + 1) * (a - d) :=
        Nat.mul_le_mul_right (a - d) hcard
      have hcharged : (e + 1) * (a - d) ≤
          (e + 1) * (a - d) * largeCost C := by
        have hmul := Nat.mul_le_mul_left ((e + 1) * (a - d)) hlargePositive
        simpa only [Nat.mul_one] using hmul
      exact hscaled.trans hcharged
    · simpa only [S, regularComponentCurveStage] using hdegree
    · simpa only [S, regularComponentCurveStage] using hunit
  have hlargeSum :
      (∑ C : RegularComponent Omega G T H, largeCost C) ≤
        flagMixed surfaceFlag cutFlag unitZFlag +
          flagMixed surfaceFlag cutFlag unitAllFlag := by
    calc
      (∑ C : RegularComponent Omega G T H, largeCost C) =
          (∑ C : RegularComponent Omega G T H, B.zCost C) +
            ∑ C : RegularComponent Omega G T H, B.allCost C := by
        simp only [largeCost, Finset.sum_add_distrib]
      _ ≤ flagMixed surfaceFlag cutFlag unitZFlag +
          flagMixed surfaceFlag cutFlag unitAllFlag :=
        Nat.add_le_add B.sum_zCost_le B.sum_allCost_le
  exact aggregate_component_stratified_incidence G T H Gamma
    (selectedPoint phi selected) hGpoint hTpoint hHp (a - d) U V (e + 1)
    (flagMixed surfaceFlag cutFlag agreementDirection6600)
    (flagMixed surfaceFlag cutFlag unitYZFlag)
    (flagMixed surfaceFlag cutFlag unitZFlag +
      flagMixed surfaceFlag cutFlag unitAllFlag)
    degreeCost unitCost largeCost hcomponent
    (by simpa only [degreeCost] using
      B.sum_weightedCost_le agreementDirection6600)
    (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
    hlargeSum

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research


/-!
# Factorwise outer residual incidence for score 66

The surface can have several irreducible factors.  The recursive incidence
bound must therefore retain each factor's own flag and only aggregate after
the factorwise bound is proved.  This is the factor-symbolic counterpart of
`recursive_scaled_primary_z_6600`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research

open scoped Classical
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactPrimeSeedIncidence
open ContactFlagBezout6543Research

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar] {flag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Exact factorwise outer compression, including the branch-local `Z` and
all-coordinate tails.  All coefficients remain symbolic in the factor flag `p`; the
conclusion is exactly `factorRegularLedger p`.
-/
theorem recursive_scaled_factor_6600
    (hphi : Function.Injective phi)
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (p : FlagDegree)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * gap ≤
        D.degree *
            ((flagMixed p agreementDirection6600 agreementDirection6600 *
                degreeIncidence +
              flagMixed p agreementDirection6600 unitYZFlag *
                unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p agreementDirection6600 unitZFlag +
                  flagMixed p agreementDirection6600 unitAllFlag)) +
          ((flagMixed p agreementDirection6600 unitYZFlag *
                degreeIncidence +
              flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
            (errors + 1) * gap *
              (flagMixed p unitYZFlag unitZFlag +
                flagMixed p unitYZFlag unitAllFlag))) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedger p := by
  have h := recursive_scaled_stratified_incidence_bound
    hphi S
    ((flagMixed p agreementDirection6600 agreementDirection6600 *
          degreeIncidence +
        flagMixed p agreementDirection6600 unitYZFlag * unitIncidence) +
      (errors + 1) * gap *
        (flagMixed p agreementDirection6600 unitZFlag +
          flagMixed p agreementDirection6600 unitAllFlag))
    ((flagMixed p agreementDirection6600 unitYZFlag * degreeIncidence +
        flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
      (errors + 1) * gap *
        (flagMixed p unitYZFlag unitZFlag +
          flagMixed p unitYZFlag unitAllFlag))
    degreeIncidence unitIncidence
    (by norm_num [agreements, n, errors, w])
    hagreement hfiber
    (by
      intro k hk
      rw [hnodes]
      exact degree_part_bound k hk)
    (by
      intro k hk
      rw [hnodes]
      exact unit_part_bound k hk)
  calc
    Gamma.card * gap ^ 2 ≤
        degreeIncidence *
            ((flagMixed p agreementDirection6600 agreementDirection6600 *
                  degreeIncidence +
                flagMixed p agreementDirection6600 unitYZFlag *
                  unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p agreementDirection6600 unitZFlag +
                  flagMixed p agreementDirection6600 unitAllFlag)) +
          unitIncidence *
            ((flagMixed p agreementDirection6600 unitYZFlag *
                  degreeIncidence +
                flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p unitYZFlag unitZFlag +
                  flagMixed p unitYZFlag unitAllFlag)) := by
      simpa only [gap] using h
    _ = factorRegularLedger p := by
      simp only [factorRegularLedger, factorPrimary, factorZTail, factorAllTail]
      ring

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research


/-!
# Factorwise score-66 provider from shared adaptive prime budgets

At a terminal node of the outer factor recursion, the proper agreement cut
is decomposed into its regular curve components.  The inner recursion and
shared prime budget then give exactly the affine fiber bound consumed by
`recursive_scaled_factor_6600`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualIterationResearch.ResidualStage
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactIdentityResidualComponentFamilyAll6600Research
open ContactIdentityResidualFactorIncidence6600Research
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 40000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The exact unresolved large-pencil leaf for one outer terminal cut.
Keeping it as a named proposition makes the final factor theorem readable:
all recursive and component bookkeeping has already been discharged.
-/
def TerminalLargeZCharge
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (D : S.TerminalDescendant) (i : Iota)
    (B : PrimeFlagBudgetFamily
      (G := D.stage.G)
      (T := agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H := regularitySurface phi D.stage.F)
      flag (residualAgreementFlag D.degree)) : Prop :=
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := agreements - (w - D.degree)
  ∀ C : RegularComponent Omega D.stage.G T
      (regularitySurface phi D.stage.F),
    let GammaC := componentSeeds Omega D.stage.G T
      (regularitySurface phi D.stage.F) GammaI
      (selectedPoint phi D.stage.selected) C
    let SC := regularComponentCurveStage D.stage.F D.stage.G T
      D.stage.selected GammaI D.stage.nodes x D.stage.u0 D.stage.u1
      pchar errors D.degree flag (residualAgreementFlag D.degree)
      D.stage.G_dvd_surface D.stage.flag_support
      (surfaceMap_agreement_in_flag_of_surface_weights
        D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
        D.stage.surface_total_weight D.degree
        (fun j ↦ (j.factorial : K)⁻¹)
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.stage.x_injective
      (fun gamma hgamma ↦ D.stage.degree_le gamma
        (Finset.mem_filter.mp hgamma).1)
      (fun gamma hgamma ↦ D.stage.solution gamma
        (Finset.mem_filter.mp hgamma).1)
      (fun gamma hgamma ↦ D.stage.regular gamma
        (Finset.mem_filter.mp hgamma).1)
      (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
        D.degree errors (Finset.filter_subset _ _) D.stage.no_large_pencil)
      D.stage.characteristic_bound C
    ∀ E : SC.TerminalDescendant,
      E.degree < E.stage.identities.card →
        GammaC.card * (aD - D.degree) ≤
          (errors + 1) * (aD - D.degree) * B.zCost C

/-- One terminal outer proper cut receives the exact factor-affine bound.
The shared component budget and all two-level actual-identity arithmetic are
fully internal; `TerminalLargeZCharge` is the only remaining leaf.
-/
theorem terminal_outer_fiber_bound_of_prime_flag_budget
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (D : S.TerminalDescendant) (i : Iota) (hi : i ∈ D.stage.nodes)
    (B : PrimeFlagBudgetFamily
      (G := D.stage.G)
      (T := agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (H := regularitySurface phi D.stage.F)
      flag (residualAgreementFlag D.degree))
    (hallPositive : ∀ C : RegularComponent Omega D.stage.G
      (agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
      (regularitySurface phi D.stage.F), 1 ≤ B.allCost C) :
    (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * gap ≤
      D.degree *
          ((flagMixed flag agreementDirection6600 agreementDirection6600 *
              degreeIncidence +
            flagMixed flag agreementDirection6600 unitYZFlag *
              unitIncidence) +
            (errors + 1) * gap *
              (flagMixed flag agreementDirection6600 unitZFlag +
                flagMixed flag agreementDirection6600 unitAllFlag)) +
        ((flagMixed flag agreementDirection6600 unitYZFlag *
              degreeIncidence +
            flagMixed flag unitYZFlag unitYZFlag * unitIncidence) +
          (errors + 1) * gap *
            (flagMixed flag unitYZFlag unitZFlag +
              flagMixed flag unitYZFlag unitAllFlag)) := by
  classical
  let GammaI := Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let aD := agreements - (w - D.degree)
  have hTflag : PolynomialInFlag (residualAgreementFlag D.degree) T := by
    exact surfaceMap_agreement_in_flag_of_surface_weights
      D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  have hsub : GammaI ⊆ Gamma := Finset.filter_subset _ _
  have hTpoint : ∀ gamma ∈ GammaI,
      MvPolynomial.eval (selectedPoint phi D.stage.selected gamma) T = 0 := by
    intro gamma hgamma
    obtain ⟨hGamma, hagree⟩ := Finset.mem_filter.mp hgamma
    exact (selected_agreement_zero_iff phi D.stage.F D.stage.selected
      pchar D.degree D.stage.characteristic_bound gamma
      (D.stage.degree_le gamma hGamma) (D.stage.solution gamma hGamma)
      (D.stage.regular gamma hGamma)
      (x i) (D.stage.u0 i) (D.stage.u1 i)).mpr hagree
  have hinnerAgreement : ∀ gamma ∈ GammaI,
      aD ≤ (D.stage.nodes.filter (fun j ↦
        (D.stage.selected gamma).eval (x j) =
          D.stage.u0 j + gamma * D.stage.u1 j)).card := by
    intro gamma hgamma
    have hGamma := hsub hgamma
    have h0 := Nat.sub_le_sub_right (hagreement gamma hGamma)
      (w - D.degree)
    exact h0.trans (by
      simpa only [aD, ResidualStage.agreementFiber,
        ResidualStage.Agrees] using D.agreement_card gamma hGamma)
  have hda : D.degree < aD := by
    have hD := D.degree_le
    norm_num [aD, agreements, n, errors, w] at *
    omega
  have hdegree : ∀ k ≤ D.degree,
      (D.stage.nodes.card - k) * (aD - D.degree) * (D.degree - k) ≤
        degreeIncidence * (aD - k) := by
    intro k hk
    have hDle : D.degree ≤ w := D.degree_le
    let total := (w - D.degree) + k
    have htotal : total ≤ w := by
      dsimp only [total]
      omega
    have h := degree_part_bound total htotal
    have hnodesD := D.nodes_card
    rw [hnodes] at hnodesD
    have hgap :
        aD - D.degree = gap := by
      have hres := residual_gap_eq agreements w (w - D.degree)
        (Nat.sub_le w D.degree) (by norm_num [agreements, n, errors, w])
      have hback : w - (w - D.degree) = D.degree := by omega
      simpa only [aD, hback, gap] using hres
    have hn : n - total = D.stage.nodes.card - k := by
      rw [hnodesD]
      dsimp only [total]
      omega
    have hw : w - total = D.degree - k := by
      dsimp only [total]
      omega
    have ha : agreements - total = aD - k := by
      dsimp only [total, aD]
      omega
    rw [hgap]
    rw [hn, hw, ha] at h
    exact h
  have hunit : ∀ k ≤ D.degree,
      (D.stage.nodes.card - k) * (aD - D.degree) ≤
        unitIncidence * (aD - k) := by
    intro k hk
    have hDle : D.degree ≤ w := D.degree_le
    let total := (w - D.degree) + k
    have htotal : total ≤ w := by
      dsimp only [total]
      omega
    have h := unit_part_bound total htotal
    have hnodesD := D.nodes_card
    rw [hnodes] at hnodesD
    have hgap :
        aD - D.degree = gap := by
      have hres := residual_gap_eq agreements w (w - D.degree)
        (Nat.sub_le w D.degree) (by norm_num [agreements, n, errors, w])
      have hback : w - (w - D.degree) = D.degree := by omega
      simpa only [aD, hback, gap] using hres
    have hn : n - total = D.stage.nodes.card - k := by
      rw [hnodesD]
      dsimp only [total]
      omega
    have ha : agreements - total = aD - k := by
      dsimp only [total, aD]
      omega
    rw [hgap]
    rw [hn, ha] at h
    exact h
  have hbound := proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all
    hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
    x D.stage.u0 D.stage.u1 pchar errors D.degree aD
    degreeIncidence unitIncidence flag (residualAgreementFlag D.degree)
    D.stage.G_dvd_surface D.stage.flag_support hTflag
    D.stage.surface_s_weight D.stage.surface_ys_weight
    D.stage.surface_total_weight D.stage.x_injective
    (fun gamma hgamma ↦ D.stage.degree_le gamma (hsub hgamma))
    (fun gamma hgamma ↦ D.stage.solution gamma (hsub hgamma))
    (fun gamma hgamma ↦ D.stage.regular gamma (hsub hgamma))
    (fun gamma hgamma ↦ D.stage.on_component gamma (hsub hgamma))
    hTpoint hinnerAgreement
    (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
      D.degree errors hsub D.stage.no_large_pencil)
    D.stage.characteristic_bound hda B (by
      simpa only [T] using hallPositive)
    hdegree hunit
  have hgapEq : aD - D.degree = gap := by
    have hres := residual_gap_eq agreements w (w - D.degree)
      (Nat.sub_le w D.degree) (by norm_num [agreements, n, errors, w])
    have hback : w - (w - D.degree) = D.degree := by
      have := D.degree_le
      omega
    simpa only [aD, hback, gap] using hres
  rw [hgapEq] at hbound
  rw [flagMixed_residualAgreement_direction,
    flagMixed_residualAgreement_unit,
    flagMixed_residualAgreement_z,
    flagMixed_residualAgreement_all] at hbound
  dsimp only [GammaI] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by ring

/-- Complete factorwise regular count, conditional only on producing one
shared adaptive budget whose all-coordinate cost is positive at every
terminal outer cut.
-/
theorem recursive_scaled_factor_6600_of_prime_flag_budgets
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbudget : ∀ (D : S.TerminalDescendant) (i : Iota),
      i ∈ D.stage.nodes →
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      ∃ B : PrimeFlagBudgetFamily
        (G := D.stage.G)
        (T := agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (H := regularitySurface phi D.stage.F)
        flag (residualAgreementFlag D.degree),
        ∀ C : RegularComponent Omega D.stage.G
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (regularitySurface phi D.stage.F), 1 ≤ B.allCost C) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedger flag := by
  apply recursive_scaled_factor_6600 hphi S flag hnodes hagreement
  intro D i hi hproper
  obtain ⟨B, hallPositive⟩ := hbudget D i hi hproper
  exact terminal_outer_fiber_bound_of_prime_flag_budget
    hphi S hnodes hagreement D i hi B hallPositive

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualFactorProvider6600Research


/-!
# Factor ledger from adaptive projection families

This is the narrow geometric seam for score 66.  At each proper terminal
outer cut, one shared adaptive `Z/YZ/All` projection family is converted to
the recursive prime budget.  Positivity of the all-coordinate fallback is
then automatic.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research

open scoped Classical
open ContactNearPencil6600ArithmeticResearch ContactPolynomialSolutions
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualFactorProvider6600Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveUnitPoleFamilyResearch

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- At every proper terminal outer cut, the actual regular components admit
one common adaptive unit projection family. -/
def TerminalAdaptiveProjectionFamilies
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w) : Prop :=
  ∀ (D : S.TerminalDescendant) (i : Iota),
    i ∈ D.stage.nodes →
    ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i) →
    ∃ base : ∀ C : RegularComponent Omega D.stage.G
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamily base flag
        (residualAgreementFlag D.degree))

/-- The adaptive family discharges both the shared prime-budget hypothesis
and the degree-zero-safe all-cost positivity required by the complete
factor recursion. -/
theorem recursive_scaled_factor_6600_of_adaptive_projection_families
    (hphi : Function.Injective phi)
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hprojection : TerminalAdaptiveProjectionFamilies S) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedger flag := by
  apply recursive_scaled_factor_6600_of_prime_flag_budgets
    hphi S hnodes hagreement
  intro D i hi hproper
  obtain ⟨base, ⟨P⟩⟩ := hprojection D i hi hproper
  refine ⟨P.toPrimeFlagBudgetFamily, ?_⟩
  intro C
  exact P.one_le_toPrimeFlagBudgetFamily_allCost C

end

end ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research


/-!
# Actual global selected-family ledger at score 66.11

The singular union is already bounded unconditionally.  This module joins it
to the factorwise recursive regular bounds.  Per-factor recursion uses its
sharp nested flag, while aggregation is performed only in the additive raw
facets.  The sole remaining input is one proved count inequality for each
actual positive-`R` factor.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research

open scoped Classical BigOperators
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactRegularFactorFlag6600Research
open ContactSingularBranch6600Research
open ContactNearPencil6600FactorLedgerResearch
open ContactNearPencil6600FlagResearch
open ContactSharpFactorAggregationPost6600Research
open ContactPrimeSeedIncidence

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

def regularSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : ContactRegularFactorFlag6600Research.RegularIndex Q) : Finset K :=
  Gamma.filter (fun gamma ↦ RegularSolution F.1 (selected gamma) gamma)

theorem regularSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : ContactRegularFactorFlag6600Research.RegularIndex Q) :
    regularSeeds Q selected Gamma F ⊆ Gamma :=
  Finset.filter_subset _ _

/-- The score-66 selected solutions are covered by the actual regular factor
families and the already constructed singular union. -/
theorem card_le_regular_sum_add_singular
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0) :
    Gamma.card ≤
      (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
        (regularSeeds Q selected Gamma F).card) +
      (singularSeeds Q selected Gamma).card := by
  classical
  let regularUnion := Finset.univ.biUnion (regularSeeds Q selected Gamma)
  have hsub : Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma := by
    intro gamma hgamma
    obtain ⟨F, hF, hreg⟩ | ⟨q, hq, himp⟩ | hexc :=
      solution_three_way Q hQ weightedCap w seedTotalCap slopeCap prime
        (by norm_num [slopeCap]) characteristic_gates.2.2.2
        (by norm_num [w])
        (by norm_num [ContactParameters6600Research.w,
          ContactParameters6600Research.weightedCap,
          ContactParameters6600Research.multiplicity,
          ContactParameters6600Research.agreements,
          ContactParameters6600Research.n,
          ContactParameters6600Research.errors,
          ContactParameters6600Research.slopeCap])
        hbox (selected gamma) gamma (hsolution gamma hgamma)
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨F, hF⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hgamma, hreg⟩⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨q, hq⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hgamma, himp⟩⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨hgamma, hexc⟩
  calc
    Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card :=
      Finset.card_le_card hsub
    _ ≤ regularUnion.card + (singularSeeds Q selected Gamma).card :=
      Finset.card_union_le _ _
    _ ≤ (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card) +
        (singularSeeds Q selected Gamma).card :=
      Nat.add_le_add_right Finset.card_biUnion_le _

/-- The actual regular factor family consumes at most the sharp regular
numerator through additive raw-facet aggregation. -/
theorem regularSeeds_scaled_rectangular_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hregular : ∀ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * gap ^ 2 ≤
        factorRegularLedger (sharpRegularFlag Q F)) :
    (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card) * gap ^ 2 ≤
        sharpRegularNumerator := by
  calc
    (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
        (regularSeeds Q selected Gamma F).card) * gap ^ 2 =
        ∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
        factorRegularLedger (sharpRegularFlag Q F) :=
      Finset.sum_le_sum (fun F _ ↦ hregular F)
    _ ≤ factorRegularLedger surfaceFlag6600 :=
      sum_actual_sharp_factorRegularLedger_le Q hQ hbox htetra
    _ = sharpRegularNumerator := rfl

/-- Full selected-family scaled count.  The singular branch, cover, and
sharp raw aggregation are all discharged; only per-regular-factor counts
remain as input. -/
theorem global_scaled_bound_of_regular_factors
    {Iota : Type} [DecidableEq Iota]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hregular : ∀ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * gap ^ 2 ≤
        factorRegularLedger (sharpRegularFlag Q F)) :
    Gamma.card * gap ^ 2 ≤ sharpTotalNumerator := by
  have hcover := card_le_regular_sum_add_singular Q hQ hbox selected Gamma
    hsolution
  have hreg := regularSeeds_scaled_rectangular_bound Q hQ hbox htetra selected Gamma
    hregular
  have hsing := singularSeeds_scaled_bound Q hQ hbox selected Gamma nodes
    x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  calc
    Gamma.card * gap ^ 2 ≤
        ((∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card) +
          (singularSeeds Q selected Gamma).card) * gap ^ 2 :=
      Nat.mul_le_mul_right (gap ^ 2) hcover
    _ = (∑ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
          (regularSeeds Q selected Gamma F).card) * gap ^ 2 +
        (singularSeeds Q selected Gamma).card * gap ^ 2 := by ring
    _ ≤ sharpRegularNumerator + retainedSingularContribution :=
      Nat.add_le_add hreg hsing
    _ = sharpTotalNumerator := rfl

theorem global_count_lt_alignment_of_regular_factors
    {Iota : Type} [DecidableEq Iota]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hregular : ∀ F : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Gamma F).card * gap ^ 2 ≤
        factorRegularLedger (sharpRegularFlag Q F)) :
    Gamma.card < alignmentBudget := by
  have hscaled := global_scaled_bound_of_regular_factors Q hQ hbox htetra selected
    Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
    hregular
  have hlt : Gamma.card * gap ^ 2 < alignmentBudget * gap ^ 2 :=
    hscaled.trans_lt sharp_strict_budget
  exact Nat.lt_of_mul_lt_mul_right hlt

end

end ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research


/-!
# Initial residual stages for actual score-66.11 regular factors

An original positive-`R` factor is covered by its actual geometric surface
factors over the constructed algebraic closure of `K(X)`.  This module turns
each such geometric factor into the exact initial `ResidualStage` consumed by
the nested actual-identity theorem, and aggregates its factorwise ledger back
to the original rectangular flag.
-/

namespace ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research

open scoped Classical BigOperators
open ContactParameters6600Research
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactPrimeSeedIncidence ContactPolynomialSolutions ContactInterpolation
open ContactTranslation ContactProperCutSeedCount
open ContactTetraGeometricSeedCover6622Research
open ContactRegularFactorFlag6600Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagBezout6543Research
open ContactNearPencil6600FactorLedgerResearch
open ContactSharpFactorAggregationPost6600Research

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- Rectangular nested flag of one geometric factor, in the literal
`(Z,Y,R)` degree order. -/
def geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : FlagDegree :=
  ⟨g.1.degreeOf (2 : Fin 3), g.1.degreeOf (0 : Fin 3),
    g.1.degreeOf (1 : Fin 3)⟩

theorem polynomialIn_geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : PolynomialInFlag (geometricFlag K g) g.1 := by
  intro d hd
  have h0 := MvPolynomial.monomial_le_degreeOf (0 : Fin 3) hd
  have h1 := MvPolynomial.monomial_le_degreeOf (1 : Fin 3) hd
  have h2 := MvPolynomial.monomial_le_degreeOf (2 : Fin 3) hd
  change d 1 ≤ g.1.degreeOf 1 ∧
    d 0 + d 1 ≤ g.1.degreeOf 0 + g.1.degreeOf 1 ∧
    d 0 + d 1 + d 2 ≤
      g.1.degreeOf 2 + g.1.degreeOf 0 + g.1.degreeOf 1
  omega

/-- The interpolation box supplies exactly the three global support values
preserved by residualization. -/
theorem residual_surface_weights_of_box
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ seedTotalCap) :
    wt residualSWeights F ≤ 9 ∧
      wt residualYSWeights F ≤ 44 ∧
      wt residualTotalWeights F ≤ 482 := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F 9).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
    rw [weight_fin4]
    rw [show residualSWeights 0 = 0 by rfl,
      show residualSWeights 1 = 0 by rfl,
      show residualSWeights 2 = 1 by rfl,
      show residualSWeights 3 = 0 by rfl]
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
    simpa only [slopeCap] using hb.2.1
  · constructor
    · apply (weightedTotalDegree_le_iff residualYSWeights F 44).mpr
      intro d hd
      have hb : d 1 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
          d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
      rw [weight_fin4]
      rw [show residualYSWeights 0 = 0 by rfl,
        show residualYSWeights 1 = 1 by rfl,
        show residualYSWeights 2 = 1 by rfl,
        show residualYSWeights 3 = 0 by rfl]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
      norm_num [weightedCap, ContactParameters6600Research.multiplicity,
        agreements, n, errors, w] at hb
      omega
    · apply (weightedTotalDegree_le_iff residualTotalWeights F 482).mpr
      intro d hd
      rw [weight_fin4]
      rw [show residualTotalWeights 0 = 0 by rfl,
        show residualTotalWeights 1 = 1 by rfl,
        show residualTotalWeights 2 = 1 by rfl,
        show residualTotalWeights 3 = 1 by rfl]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
      simpa only [seedTotalCap] using htetra d hd

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Canonical initial outer residual state on one actual geometric factor. -/
def geometricResidualStage
    [CharP K prime]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hRpos : 0 < F.degreeOf (2 : Fin 4))
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (g : GeometricFactor K F) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K F selected Gamma g) x prime errors
      (sharpGeometricFlag K g) w := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hgspec := surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
  have hgirred := hgspec.1
  have hgdiv := hgspec.2
  have hRsmall : F.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box F weightedCap w seedTotalCap slopeCap hbox).trans_lt
      (by norm_num [slopeCap, prime])
  have hgate := geometric_factor_regular_gate K (GenericField K) F hF prime
    hRpos hRsmall g.1 hgirred
    (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
  have hsub := geometricSeeds_subset K F selected Gamma g
  have hwts := residual_surface_weights_of_box K F hbox htetra
  exact {
    nodes := nodes
    u0 := u0
    u1 := u1
    selected := selected
    F := F
    G := g.1
    irreducible_G := hgirred
    G_dvd_surface := hgdiv
    y_dependent := hgate.1
    regular_proper := by
      simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
    flag_support := polynomialIn_sharpGeometricFlag F g
    surface_s_weight := hwts.1
    surface_ys_weight := hwts.2.1
    surface_total_weight := hwts.2.2
    x_injective := hinj
    degree_le := fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
    solution := fun gamma hgamma ↦ hsolutions gamma (hsub hgamma)
    regular := fun gamma hgamma ↦
      selectedPoint_regular_of_specialization K F selected gamma
        (hregular gamma (hsub hgamma))
    on_component := fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2
    no_large_pencil := noLargeSelectedPencil_mono selected Gamma _ w errors
      hsub hnoPencil
    characteristic_bound := by norm_num [w, prime]
  }

end


end ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research


/-!
# Actual regular-factor residual stages at score 66

This adapter specializes the canonical geometric residual stage to one of
the real positive-`R` factors in the global selected-family decomposition.
All solution, regularity, degree, agreement, and no-pencil fields are
inherited from the filtered original family.
-/

namespace ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

open scoped Classical
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactInterpolation ContactTranslation
open ContactGenericInitialPoint ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactTetraGeometricSeedCover6622Research ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research ContactGlobalSelectedFamilies6600Research
open ContactIdentityResidualIterationResearch ContactFlagBezout6543Research
open ContactIdentityResidualGlobalFlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactSharpFactorAggregationPost6600Research

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- The exact initial stage for one geometric factor of one actual global
regular factor. -/
def regularGeometricResidualStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hQtetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x prime errors (sharpGeometricFlag K g) w := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata :=
    directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
  have hRirred := hRdata.1
  have hRpos := hRdata.2.1
  have hRbox := hRdata.2.2
  have hraw := positiveRFactor_raw_budgets Q hQ hbox hQtetra
  have hRtotal : factorRawTotal Q R ≤ seedTotalCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hraw.2.2
  have hRtetra : ∀ d ∈ R.1.support,
      d 1 + d 2 + d 3 ≤ seedTotalCap := by
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
    rw [residualTotal_weight] at h
    exact h.trans hRtotal
  have hsub := regularSeeds_subset Q selected Gamma R
  exact geometricResidualStage K R.1 hRirred hRpos hRbox hRtetra selected
    (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
    (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.1)
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ w errors hsub hnoPencil) g

/-- Geometric recursive bounds aggregate to the exact original rectangular
factor ledger expected by the global selected-family join. -/
theorem regular_factor_seed_bound_of_geometric_counts
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (hcount : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card *
          gap ^ 2 ≤ factorRegularLedger (sharpGeometricFlag K g)) :
    (regularSeeds Q selected Gamma R).card * gap ^ 2 ≤
      factorRegularLedger (sharpRegularFlag Q R) := by
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  exact original_regular_seed_bound_of_sharp_geometric_factor_counts
    Q R selected (regularSeeds Q selected Gamma R) hsolutions hcount

end

end ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research


/-!
# End-to-end score-66 selected count from adaptive projection families

This module joins the actual positive-`R` factor decomposition, its geometric
surface factors, canonical residual stages, recursive adaptive projection
budgets, the rectangular factor ledger, and the unconditional singular
branch.  The only remaining input is the construction of an adaptive unit
projection family at every terminal proper cut.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research

open scoped Classical
open ContactParameters6600Research
open ContactGenericInitialPoint ContactPrimeSeedIncidence
open ContactTetraGeometricSeedCover6622Research ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research ContactGlobalSelectedFamilies6600Research
open ContactRegularFactorResidualStage6600Research
open ContactAdaptiveProjectionFactorProvider6600Research
open ContactIdentityResidualIterationResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactSharpFactorAggregationPost6600Research
open ContactInterpolation ContactTranslation

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

variable {K Iota : Type} [Field K] [CharP K prime]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)
local instance : CharP (GenericField K) prime := genericField_charP K prime

/-- One actual global regular factor receives its exact factor ledger once
all of its canonical geometric stages have adaptive projection families. -/
theorem regular_factor_seed_bound_of_adaptive_projection_families
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hQtetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (hprojection : ∀ g : GeometricFactor K R.1,
      TerminalAdaptiveProjectionFamilies
        (regularGeometricResidualStage Q hQ hbox hQtetra selected Gamma nodes
          x u0 u1 hinj hdegree hnoPencil R g)) :
    (regularSeeds Q selected Gamma R).card * gap ^ 2 ≤
      factorRegularLedger (sharpRegularFlag Q R) := by
  apply regular_factor_seed_bound_of_geometric_counts Q hQ hbox
    selected Gamma R
  intro g
  let S := regularGeometricResidualStage Q hQ hbox hQtetra selected Gamma nodes
    x u0 u1 hinj hdegree hnoPencil R g
  have hgeomSub : geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
    (geometricSeeds_subset K R.1 selected
      (regularSeeds Q selected Gamma R) g).trans
      (regularSeeds_subset Q selected Gamma R)
  have hnodesS : S.nodes.card = n := by
    simpa [S, regularGeometricResidualStage, geometricResidualStage] using hnodes
  have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g,
      agreements ≤ (S.agreementFiber gamma).card := by
    intro gamma hgamma
    simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
      regularGeometricResidualStage, geometricResidualStage] using
        hagreement gamma (hgeomSub hgamma)
  exact recursive_scaled_factor_6600_of_adaptive_projection_families
    (polynomialEmbedding_injective K) S hnodesS hagreementS (hprojection g)

/-- Full actual selected-family count.  Covering, singular seeds, recursive
identity residualization, geometric/original factor aggregation, and the
strict score-66 arithmetic are all internal. -/
theorem global_count_lt_alignment_of_adaptive_projection_families
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hQtetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hprojection : ∀
      (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
      (g : GeometricFactor K R.1),
      TerminalAdaptiveProjectionFamilies
        (regularGeometricResidualStage Q hQ hbox hQtetra selected Gamma nodes
          x u0 u1 hinj hdegree hnoPencil R g)) :
    Gamma.card < alignmentBudget := by
  apply global_count_lt_alignment_of_regular_factors Q hQ hbox hQtetra selected
    Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
  intro R
  exact regular_factor_seed_bound_of_adaptive_projection_families
    Q hQ hbox hQtetra selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil R (hprojection R)

end

end ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research


/-!
# Frozen score-66 alignment from terminal adaptive projection families

This adapter specializes the end-to-end geometric count to the benchmark
field and its full evaluation domain.  Its sole remaining premise is the
construction of an adaptive unit projection family at every terminal proper
cut of every actual regular geometric factor.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6600Research

open scoped Classical
open ProximityPrize.Benchmark
open ContactParameters6600Research
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactGenericInitialPoint ContactTetraGeometricSeedCover6622Research
open ContactGlobalSelectedFamilies6600Research
open ContactRegularFactorResidualStage6600Research
open ContactAdaptiveProjectionFactorProvider6600Research
open ContactGlobalAdaptiveProjection6600Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : DecidableEq (GenericField IRSProfile.Field) := Classical.decEq _
local instance : CharP IRSProfile.Field prime :=
  ContactFrozenAlignment6600Research.challenge_field_characteristic6600
local instance : CharP (GenericField IRSProfile.Field) prime :=
  genericField_charP IRSProfile.Field prime

/-- The exact geometric premise left after freezing the interpolation and
alignment frontend.  No counting or numerical assertion is exposed here. -/
def FrozenTerminalAdaptiveProjectionFamilies6600 : Prop :=
  ∀ (Q : MvPolynomial (Fin 4) IRSProfile.Field) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox IRSProfile.Field
      weightedCap w seedTotalCap slopeCap)
    (htetra : ∀ d ∈ Q.support, d 1 + d 2 + d 3 ≤ seedTotalCap)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hnoPencil : NoLargeSelectedPencil selected seeds w errors)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (g : GeometricFactor IRSProfile.Field R.1),
    TerminalAdaptiveProjectionFamilies
      (regularGeometricResidualStage Q hQ hbox htetra selected seeds
        (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)

/-- Terminal adaptive projection families imply the exact frozen global
selected-family count consumed by the stock alignment bridge. -/
theorem global_count_lt_alignment6600_of_terminal_projection_families
    (hprojection : FrozenTerminalAdaptiveProjectionFamilies6600) :
    ContactFrozenAlignment6600Research.GlobalCountLtAlignment6600 := by
  intro Q hQ hbox htetra selected seeds u0 u1 hdegree hsolution hagreement hnoPencil
  apply global_count_lt_alignment_of_adaptive_projection_families
    Q hQ hbox htetra selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, n])
      hdegree hsolution hagreement hnoPencil
  intro R g
  exact hprojection Q hQ hbox htetra selected seeds u0 u1 hdegree hnoPencil R g

end

end ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6600Research


/-!
# Solution-shaped score-66 endpoint

This joins the entire frozen interpolation/alignment/protocol frontend.  Its
only premise is the global selected-family counting proposition; once the
regular-factor geometry proves that proposition, the conclusion can be used
verbatim as the submission's `candidate` theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch

open ProximityPrize.Benchmark

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A `Solution.lean`-compatible score-66 claim conditional only on the
remaining global selected-family count. -/
theorem protocolClaim6600_of_global_count_lt_alignment
    (global_count_lt_alignment :
      ContactFrozenAlignment6600Research.GlobalCountLtAlignment6600) :
    ProtocolClaim 6638 316619 1048576 := by
  have halign : AffineLineAlignmentBound IRSProfile.baseCode
      ContactParameters6600Research.errors
      ContactParameters6600Research.alignmentBudget :=
    ContactFrozenAlignment6600Research.alignment_of_global_count_lt_alignment6600
      global_count_lt_alignment
  exact AlignmentProtocol6600ConditionalResearch.protocolClaim6600_of_alignment
    halign

end ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch


/-!
# Score-66 protocol endpoint from terminal adaptive projection families

This is the final composition seam.  Once the terminal adaptive projection
families are constructed, the global geometric count, frozen interpolation
alignment, and protocol soundness proof are all discharged internally.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6600AdaptiveResearch

open ProximityPrize.Benchmark
open ContactGlobalAdaptiveAlignment6600Research

set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

/-- A submission-shaped score-66 theorem whose sole premise is the terminal
adaptive projection-family constructor. -/
theorem protocolClaim6600_of_terminal_projection_families
    (hprojection : FrozenTerminalAdaptiveProjectionFamilies6600) :
    ProtocolClaim 6638 316619 1048576 := by
  apply ContactProtocol6600ConditionalResearch.protocolClaim6600_of_global_count_lt_alignment
  exact global_count_lt_alignment6600_of_terminal_projection_families hprojection

end ProximityPrize.SubmissionLower.ContactProtocol6600AdaptiveResearch


/-!
# Derivative gate intrinsic to a residual stage

The adaptive flag projection requires a nonzero derivative in the residual
`S` coordinate.  This is already forced by the two divisibility fields of a
`ResidualStage`: if the component equation had zero `S` derivative, then its
divisibility into the surface equation would make it divide the surface
regularity derivative, contradicting `regular_proper`.
-/

namespace ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research

open ContactGenericSurface ContactRegularFactorGate
open ContactIdentityResidualIterationResearch
open ContactFlagBezout6543Research

noncomputable section

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {p e d : ℕ} [CharP Omega p] {flag : FlagDegree}

/-- Every residual stage has the nonzero literal-`S` derivative needed by
the adaptive nested projection constructor.  No recursive path certificate
is needed. -/
theorem residualStage_pderiv_one_ne_zero
    (S : ResidualStage phi Gamma x p e flag d) :
    MvPolynomial.pderiv (1 : Fin 3) S.G ≠ 0 := by
  intro hzero
  apply S.regular_proper
  rw [← surfaceMap_pderiv_R]
  obtain ⟨Q, hQ⟩ := S.G_dvd_surface
  refine ⟨MvPolynomial.pderiv (1 : Fin 3) Q, ?_⟩
  rw [hQ, MvPolynomial.pderiv_mul, hzero, zero_mul, zero_add]

end

end ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research

/-!
# Characteristic-free terminal literal projection

A safe literal-`Z` gate and survival of the surface `S` derivative provide a
finite-separable literal normalization on every retained regular component.
No literal-`Y` resultant or mixed-degree characteristic gate is used.
-/

namespace ProximityPrize.SubmissionLower.CharFreeTerminal

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualPlaneCoordinateKernel
open ContactRegularComponentCover ContactWeakSeparableSeparatorResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveProjectionCoordinateResearch
open ContactFlagProjectionPositivity6543Research
open ContactGenericSurface ContactProperCutSeedCount ContactRegularFactorGate

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]

/-- A polynomial relation whose derivative is nonzero at the root makes the
root separable, without any degree/characteristic hypothesis. -/
theorem isSeparable_of_aeval_derivative_ne_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (f : Polynomial F)
    (hf : f ≠ 0) (hroot : Polynomial.aeval x f = 0)
    (hderiv : Polynomial.aeval x f.derivative ≠ 0) :
    IsSeparable F x := by
  have hxint : IsIntegral F x :=
    IsAlgebraic.isIntegral ⟨f, hf, hroot⟩
  have hm : minpoly F x ∣ f := minpoly.dvd F x hroot
  have hmderiv : (minpoly F x).derivative ≠ 0 := by
    intro hzero
    obtain ⟨q, rfl⟩ := hm
    apply hderiv
    simp [Polynomial.derivative_mul, hzero, minpoly.aeval F x]
  exact (Polynomial.separable_iff_derivative_ne_zero
    (minpoly.irreducible hxint)).2 hmderiv

variable {G T H Surface : MvPolynomial (Fin 3) Omega}

/-- On a retained regular component, if `Surface = G*Q` and
`H = dSurface/dS`, then `dG/dS` cannot vanish in the component prime. -/
theorem pderiv_one_not_mem_of_regular_factor
    (P : Ideal (MvPolynomial (Fin 3) Omega))
    (hGmem : G ∈ P) (hHnot : H ∉ P)
    (hfactor : G ∣ Surface)
    (hH : H = MvPolynomial.pderiv (1 : Fin 3) Surface) :
    MvPolynomial.pderiv (1 : Fin 3) G ∉ P := by
  rintro hGp
  obtain ⟨Q, rfl⟩ := hfactor
  apply hHnot
  rw [hH, MvPolynomial.pderiv_mul]
  exact P.add_mem (P.mul_mem_right _ hGp) (P.mul_mem_right _ hGmem)

/-- If `Y` is transcendental, `Z` is constant over the algebraically closed
base, and the `S`-partial of a relation survives in the prime quotient, then
the literal `Y` projection is finite separable in every characteristic. -/
theorem finite_separable_at_Y_of_Z_algebraic
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (G : MvPolynomial (Fin 3) Omega)
    (hGmem : G ∈ P)
    (hGderiv : MvPolynomial.pderiv (1 : Fin 3) G ∉ P)
    (hY : Transcendental Omega (coordinate Omega P 0))
    (hZ : IsAlgebraic Omega (coordinate Omega P 2)) :
    letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
      rationalBaseAlgebra Omega P 0 hY
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) ∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := by
  let L := CoordinateField Omega P
  let y : L := coordinate Omega P 0
  let s : L := coordinate Omega P 1
  let z : L := coordinate Omega P 2
  letI : Algebra (RatFunc Omega) L := rationalBaseAlgebra Omega P 0 hY
  letI : IsScalarTower Omega (RatFunc Omega) L :=
    rationalBaseScalarTower Omega P 0 hY
  obtain ⟨c, hc⟩ := coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZ
  let z0 : RatFunc Omega := algebraMap Omega (RatFunc Omega) c
  let coeffEval : Polynomial (RatFunc Omega) →+* RatFunc Omega :=
    Polynomial.evalRingHom z0
  let order : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
  let f : Polynomial (RatFunc Omega) := (planeMap Omega order G).map coeffEval
  have hcoeff :
      (algebraMap (RatFunc Omega) L).comp coeffEval =
        Polynomial.eval₂RingHom
          (rationalBaseEmbedding Omega P 0 hY).toRingHom z := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coeffEval, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change rationalBaseEmbedding Omega P 0 hY a =
        rationalBaseEmbedding Omega P 0 hY a
      rfl
    · simp only [RingHom.comp_apply, coeffEval, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      change algebraMap (RatFunc Omega) L z0 = z
      change algebraMap (RatFunc Omega) L
          (algebraMap Omega (RatFunc Omega) c) = coordinate Omega P 2
      exact (IsScalarTower.algebraMap_apply Omega (RatFunc Omega) L c).symm.trans hc
  have heval (A : PlaneRing Omega) :
      Polynomial.aeval s (A.map coeffEval) =
        actualPlaneEvaluation Omega order P hY A := by
    change Polynomial.eval₂ (algebraMap (RatFunc Omega) L) s
        (A.map coeffEval) = _
    rw [Polynomial.eval₂_map, hcoeff]
    simp [actualPlaneEvaluation, Polynomial.eval₂_eq_eval_map, order, s, z]
  have hfroot : Polynomial.aeval s f = 0 := by
    rw [show Polynomial.aeval s f =
        actualPlaneEvaluation Omega order P hY (planeMap Omega order G) by
      exact heval (planeMap Omega order G)]
    exact (actualPlane_root_iff Omega order P hY G).2 hGmem
  have hfderiv : Polynomial.aeval s f.derivative ≠ 0 := by
    have hmap : f.derivative =
        (planeMap Omega order (MvPolynomial.pderiv (1 : Fin 3) G)).map coeffEval := by
      simp only [f, Polynomial.derivative_map]
      rw [derivative_planeMap]
      rfl
    rw [hmap, heval]
    exact fun hzero => hGderiv
      ((actualPlane_root_iff Omega order P hY
        (MvPolynomial.pderiv (1 : Fin 3) G)).1 hzero)
  have hfne : f ≠ 0 := by
    intro hzero
    apply hfderiv
    simp [hzero]
  have hssep : IsSeparable (RatFunc Omega) s :=
    isSeparable_of_aeval_derivative_ne_zero s f hfne hfroot hfderiv
  have hsint : IsIntegral (RatFunc Omega) s := hssep.isIntegral
  have hzbot : z ∈ (⊥ : IntermediateField (RatFunc Omega) L) := by
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap Omega (RatFunc Omega) c, ?_⟩
    rw [← IsScalarTower.algebraMap_apply Omega (RatFunc Omega) L]
    exact hc
  have hpair : IntermediateField.adjoin (RatFunc Omega) ({z, s} : Set L) = ⊤ := by
    simpa only [order, Equiv.refl_apply] using
      (adjoin_two_coordinates_over_ratFunc_eq_top Omega P 0 2 1 hY
        (by intro i; fin_cases i <;> simp))
  have hsingle : IntermediateField.adjoin (RatFunc Omega) ({s} : Set L) = ⊤ := by
    apply top_unique
    rw [← hpair]
    apply IntermediateField.adjoin_le_iff.mpr
    intro a ha
    rcases ha with (rfl | ha)
    · exact (bot_le : (⊥ : IntermediateField (RatFunc Omega) L) ≤
        IntermediateField.adjoin (RatFunc Omega) ({s} : Set L)) hzbot
    · have : a = s := Set.mem_singleton_iff.mp ha
      subst a
      exact IntermediateField.subset_adjoin (RatFunc Omega) {s}
        (Set.mem_singleton s)
  let A : IntermediateField (RatFunc Omega) L :=
    IntermediateField.adjoin (RatFunc Omega) ({s} : Set L)
  letI : FiniteDimensional (RatFunc Omega) A :=
    IntermediateField.adjoin.finiteDimensional hsint
  have hfinite : FiniteDimensional (RatFunc Omega) L := by
    letI : FiniteDimensional (RatFunc Omega)
        (⊤ : IntermediateField (RatFunc Omega) L) := by
      rw [← hsingle]
      infer_instance
    exact Module.Finite.of_surjective
      (IntermediateField.topEquiv (F := RatFunc Omega) (E := L)).toLinearMap
      (IntermediateField.topEquiv (F := RatFunc Omega) (E := L)).surjective
  letI : FiniteDimensional (RatFunc Omega) L := hfinite
  have hsepA : Algebra.IsSeparable (RatFunc Omega) A :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (RatFunc Omega) L).2 hssep
  have hsepTop : Algebra.IsSeparable (RatFunc Omega)
      (⊤ : IntermediateField (RatFunc Omega) L) := by
    rw [← hsingle]
    exact hsepA
  letI : Algebra.IsSeparable (RatFunc Omega)
      (⊤ : IntermediateField (RatFunc Omega) L) := hsepTop
  have hsepL : Algebra.IsSeparable (RatFunc Omega) L :=
    AlgEquiv.Algebra.isSeparable
      (IntermediateField.topEquiv (F := RatFunc Omega) (E := L))
  exact ⟨hfinite, hsepL⟩

/-- A safe literal-`Z` gate plus survival of the surface `S` derivative
supplies one literal finite-separable coordinate on every retained regular
component. -/
theorem exists_separableLiteralCoordinate_of_Z_gate_regular_factor
    {G T H Surface : MvPolynomial (Fin 3) Omega}
    (C : RegularComponent Omega G T H)
    (hfactor : G ∣ Surface)
    (hH : H = MvPolynomial.pderiv (1 : Fin 3) Surface)
    (hZgate : LiteralProjectionGate C 2) :
    Nonempty (SeparableLiteralCoordinate C.1) := by
  by_cases hz : Transcendental Omega (coordinate Omega C.1 2)
  · exact ⟨⟨2, hz, (hZgate hz).1, (hZgate hz).2⟩⟩
  have hzalg : IsAlgebraic Omega (coordinate Omega C.1 2) := not_not.mp hz
  by_cases hy : Transcendental Omega (coordinate Omega C.1 0)
  · have hGderiv : MvPolynomial.pderiv (1 : Fin 3) G ∉ C.1 :=
      pderiv_one_not_mem_of_regular_factor C.1
        (regularComponent_G_mem Omega G T H C)
        (regularComponent_H_not_mem Omega G T H C) hfactor hH
    have hYgate := finite_separable_at_Y_of_Z_algebraic
      C.1 G (regularComponent_G_mem Omega G T H C) hGderiv hy hzalg
    exact ⟨⟨0, hy, hYgate.1, hYgate.2⟩⟩
  have hyalg : IsAlgebraic Omega (coordinate Omega C.1 0) := not_not.mp hy
  obtain ⟨i, hi⟩ :=
    exists_transcendental_coordinate_of_ne_point_kernel Omega C.1
      (regularComponent_ne_point Omega G T H C)
  have hi1 : i = (1 : Fin 3) := by
    fin_cases i <;> simp_all
  subst i
  have hSgate := finite_separable_at_S_of_other_coordinates_algebraic
    C.1 hi hyalg hzalg
  exact ⟨⟨1, hi, hSgate.1, hSgate.2⟩⟩

/-- The replacement for the old literal-`Y` gate in the first affine
projection: either a `Y/Z` differential is active, or both are algebraic. -/
theorem YZ_differential_active_or_both_algebraic
    {G T H Surface : MvPolynomial (Fin 3) Omega}
    (C : RegularComponent Omega G T H)
    (hfactor : G ∣ Surface)
    (hH : H = MvPolynomial.pderiv (1 : Fin 3) Surface)
    (hZgate : LiteralProjectionGate C 2) :
    (KaehlerDifferential.D Omega (CoordinateField Omega C.1)
        (coordinate Omega C.1 0) ≠ 0 ∨
      KaehlerDifferential.D Omega (CoordinateField Omega C.1)
        (coordinate Omega C.1 2) ≠ 0) ∨
      (IsAlgebraic Omega (coordinate Omega C.1 0) ∧
        IsAlgebraic Omega (coordinate Omega C.1 2)) := by
  by_cases hz : Transcendental Omega (coordinate Omega C.1 2)
  · exact Or.inl (Or.inr (differential_ne_zero_of_gate _ hz (hZgate hz)))
  have hzalg : IsAlgebraic Omega (coordinate Omega C.1 2) := not_not.mp hz
  by_cases hy : Transcendental Omega (coordinate Omega C.1 0)
  · have hGderiv : MvPolynomial.pderiv (1 : Fin 3) G ∉ C.1 :=
      pderiv_one_not_mem_of_regular_factor C.1
        (regularComponent_G_mem Omega G T H C)
        (regularComponent_H_not_mem Omega G T H C) hfactor hH
    have hYgate := finite_separable_at_Y_of_Z_algebraic
      C.1 G (regularComponent_G_mem Omega G T H C) hGderiv hy hzalg
    exact Or.inl (Or.inl (differential_ne_zero_of_gate _ hy hYgate))
  · exact Or.inr ⟨not_not.mp hy, hzalg⟩

/-- Production-shaped wrapper for the actual regularity surface. -/
theorem exists_terminal_separableLiteralCoordinate_of_Z_gate
    {K : Type} [Field K]
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Omega)
    (C : RegularComponent Omega G T (regularitySurface phi F))
    (hfactor : G ∣ surfaceMap phi F)
    (hZgate : LiteralProjectionGate C 2) :
    Nonempty (SeparableLiteralCoordinate C.1) := by
  apply exists_separableLiteralCoordinate_of_Z_gate_regular_factor
    C hfactor
  · exact (surfaceMap_pderiv_R phi F).symm
  · exact hZgate

end

end ProximityPrize.SubmissionLower.CharFreeTerminal

/-!
# Terminal adaptive projection families from the score-66 flag caps

This is the last local geometry adapter for the score-66 route.  A terminal
outer residual stage already carries the surface flag and its proper
agreement cut has the canonical residual flag.  The rectangular factor caps
put the literal `Y` and `Z` projection resultants below the fixed
characteristic.  Those two gates select a finite-separable literal base on
every regular curve component, after which the common adaptive nested-family
constructor applies directly.
-/

namespace ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum
open ContactParameters6600Research
open ContactPrimeSeedIncidence
open ContactGenericSurface
open ContactProperCutSeedCount
open ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedUnitFamily6600Research
open ContactAdaptiveProjectionFactorProvider6600Research
open ContactWeakSeparableSeparatorResearch
open ContactResidualStageDerivative6600Research
open CharFreeTerminal

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

theorem terminal_mixedZ_cap_exact :
    9 * (1 + 87 * w) + 44 * (17 * w) = 200669710 ∧
      200669710 < prime := by
  norm_num [w, prime]

/-- Coordinatewise rectangular consequences of nested flag support. -/
theorem degree_bounds_of_polynomialInFlag
    {p : FlagDegree} {F : MvPolynomial (Fin 3) Omega}
    (hF : PolynomialInFlag p F) :
    F.degreeOf 0 ≤ p.yz + p.all ∧
      F.degreeOf 1 ≤ p.all ∧
      F.degreeOf 2 ≤ p.zOnly + p.yz + p.all := by
  refine ⟨?_, ?_, ?_⟩
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (hF e he).1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_left (e 2) (e 0 + e 1)).trans (by
      simpa only [Nat.add_assoc] using (hF e he).2.2)

/-- The robust rectangular surface caps are already enough to construct the
entire adaptive family at every proper terminal agreement cut. -/
theorem terminalAdaptiveProjectionFamilies_of_rectangular_caps
    [CharP Omega prime]
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x prime errors flag w)
    (hflagTotal : flag.zOnly + flag.yz + flag.all ≤ 482)
    (hflagYR : flag.yz + flag.all ≤ 44)
    (hflagS : flag.all ≤ 9) :
    TerminalAdaptiveProjectionFamilies S := by
  classical
  intro D i hi hproper
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let H := regularitySurface phi D.stage.F
  have hGflag : PolynomialInFlag flag D.stage.G := D.stage.flag_support
  have hTflag : PolynomialInFlag (residualAgreementFlag D.degree) T := by
    exact surfaceMap_agreement_in_flag_of_surface_weights
      D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY, hTS, hTZ⟩ := degree_bounds_of_polynomialInFlag hTflag
  have hD : D.degree ≤ w := D.degree_le.trans (Nat.le_refl w)
  have hGY' : D.stage.G.degreeOf 0 ≤ 44 := by omega
  have hGS' : D.stage.G.degreeOf 1 ≤ 9 := by omega
  have hGZ' : D.stage.G.degreeOf 2 ≤ 482 := by omega
  have hTY' : T.degreeOf 0 ≤ 1 + 87 * w := by
    dsimp only [residualAgreementFlag] at hTY
    omega
  have hTS' : T.degreeOf 1 ≤ 17 * w := by
    dsimp only [residualAgreementFlag] at hTS
    omega
  have hTZ' : T.degreeOf 2 ≤ 1 + 963 * w := by
    dsimp only [residualAgreementFlag] at hTZ
    omega
  have hGdegree : ∀ j : Fin 3, D.stage.G.degreeOf j < prime := by
    intro j
    fin_cases j
    · exact hGY'.trans_lt (by norm_num [prime])
    · exact hGS'.trans_lt (by norm_num [prime])
    · exact hGZ'.trans_lt (by norm_num [prime])
  have hmixedZ :
      coordinateMixedDegree Omega D.stage.G T 2 < prime := by
    rw [coordinateMixedDegree_two]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt
    norm_num [w, prime]
  let hZ : ∀ C : RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      prime D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproper hGdegree hmixedZ
  have hbase : ∀ C : RegularComponent Omega D.stage.G T H,
      Nonempty (SeparableLiteralCoordinate C.1) := by
    intro C
    exact exists_terminal_separableLiteralCoordinate_of_Z_gate
      phi D.stage.F D.stage.G T C D.stage.G_dvd_surface (hZ C)
  let base : ∀ C : RegularComponent Omega D.stage.G T H,
      SeparableLiteralCoordinate C.1 := fun C ↦ Classical.choice (hbase C)
  let hYZ : ∀ C : RegularComponent Omega D.stage.G T H,
      (KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 0) ≠ 0 ∨
        KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 2) ≠ 0) ∨
      (IsAlgebraic Omega (coordinate Omega C.1 0) ∧
        IsAlgebraic Omega (coordinate Omega C.1 2)) := by
    intro C
    exact YZ_differential_active_or_both_algebraic C
      D.stage.G_dvd_surface
      (by
        dsimp only [H, regularitySurface]
        exact (ContactRegularFactorGate.surfaceMap_pderiv_R
          phi D.stage.F).symm)
      (hZ C)
  refine ⟨base, ?_⟩
  exact exists_adaptiveUnitProjectionFamily_of_nested flag
    (residualAgreementFlag D.degree) base hZ hYZ
    (residualStage_pderiv_one_ne_zero D.stage)
    D.stage.irreducible_G hproper
    ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
    ((support_subset_flagSupport_iff (residualAgreementFlag D.degree) T).2 hTflag)

end

end ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research


/-!
# Unconditional score-66.11 protocol endpoint

The terminal constructor applies to each actual geometric factor because its
coordinate degrees are bounded by the containing regular factor, while every
regular factor is pointwise bounded by the global rectangular flag sums.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6600Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactParameters6600Research
open ContactGenericInitialPoint ContactTetraGeometricSeedCover6622Research
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research
open ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research
open ContactSelectedSeedDecomposition
open ContactGlobalAdaptiveAlignment6600Research
open ContactTerminalAdaptiveProjection6600Research
open ContactSharpFactorAggregationPost6600Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : DecidableEq (GenericField IRSProfile.Field) := Classical.decEq _
local instance : CharP IRSProfile.Field prime :=
  ContactFrozenAlignment6600Research.challenge_field_characteristic6600
local instance : CharP (GenericField IRSProfile.Field) prime :=
  genericField_charP IRSProfile.Field prime

/-- The terminal projection-family premise, closed for every actual regular
geometric factor by the rectangular score-66 flag caps. -/
theorem frozenTerminalAdaptiveProjectionFamilies6600 :
    FrozenTerminalAdaptiveProjectionFamilies6600 := by
  intro Q hQ hbox htetra selected seeds u0 u1 hdegree hnoPencil R g
  have hRdata := directFactor_data Q R.1 hQ weightedCap w seedTotalCap
    slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hglobal := positiveRFactor_raw_budgets Q hQ hbox htetra
  have hRrawR : factorRawR Q R ≤ slopeCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.1
  have hRrawYR : factorRawYR Q R ≤ yCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.1
  have hRrawTotal : factorRawTotal Q R ≤ seedTotalCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.2
  have hgeom := geometricFactor_raw_budgets R.1 hRne
  have hgRawR : geometricRawR IRSProfile.Field g ≤ 9 :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeom.1).trans hRrawR
  have hgRawYR : geometricRawYR IRSProfile.Field g ≤ 44 :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeom.2.1).trans hRrawYR
  have hgRawTotal : geometricRawTotal IRSProfile.Field g ≤ 482 :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans hgeom.2.2).trans hRrawTotal
  have hgTotal : (sharpGeometricFlag IRSProfile.Field g).zOnly +
      (sharpGeometricFlag IRSProfile.Field g).yz +
      (sharpGeometricFlag IRSProfile.Field g).all ≤ 482 := by
    dsimp [sharpGeometricFlag]
    have hRYR := geometricRawR_le_geometricRawYR R.1 g
    have hYRTotal := geometricRawYR_le_geometricRawTotal R.1 g
    omega
  have hgYR : (sharpGeometricFlag IRSProfile.Field g).yz +
      (sharpGeometricFlag IRSProfile.Field g).all ≤ 44 := by
    dsimp [sharpGeometricFlag]
    have hRYR := geometricRawR_le_geometricRawYR R.1 g
    omega
  have hgS : (sharpGeometricFlag IRSProfile.Field g).all ≤ 9 := hgRawR
  exact terminalAdaptiveProjectionFamilies_of_rectangular_caps
    (regularGeometricResidualStage Q hQ hbox htetra selected seeds
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn hdegree hnoPencil R g)
    hgTotal hgYR hgS

/-- Fully closed score-66.38 lower-track claim. -/
theorem protocolClaim6600 : ProtocolClaim 6638 316619 1048576 :=
  ContactProtocol6600AdaptiveResearch.protocolClaim6600_of_terminal_projection_families
    frozenTerminalAdaptiveProjectionFamilies6600

end


end ProximityPrize.SubmissionLower.ContactProtocol6600Research

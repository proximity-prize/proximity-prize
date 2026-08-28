import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagGlobalPoleProjection6543Research
import ProximityPrize.SubmissionLower.ContactFlagPrincipalCycleAdapter6543Research
import ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research

/-!
# Complete three ordinary principal cycles for the 65.43 flag route

This module combines common nested projection coefficients, exact unit-flag
pole polynomials, and exact trapezoid family resultants.  The only remaining
premise is positivity of the selected outer variable in each of the three
plane presentations; all support and numeric cap obligations are proved.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles6543Research

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactLocalPoleBound ContactDependentGenericity6543Research
open ContactSparsePoleSupportResearch
open ContactFlagBezout6543Research ContactFlagPoleInequality6543Research
open ContactFlagTriangularProjectionResearch
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagExactSeparableProjection6543Research
open ContactFlagGlobalPoleProjection6543Research
open ContactFlagPrincipalCycleAdapter6543Research
open ContactFlagProjectionProvider6543Research
open ContactFlagTrapezoidCaps6543Research
open ContactResidualSparseComponentAdapterResearch
open TrivariateRationalCollection ActualPlaneCoordinateKernel
  ArbitraryRationalProjectionResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}
variable {hseparator : ∀ C : RegularComponent Omega G T H,
  Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj : ∀ C : RegularComponent Omega G T H,
  ProjectionsFiniteSeparable Omega C.1}

/-- Opaque literal alias used to prevent elaboration from unfolding the
large computed agreement flag while constructing its generic polynomial. -/
def exactAgreementFlag6543 : FlagDegree := ⟨91749700, 5504983, 1179639⟩

theorem exactAgreementFlag6543_eq :
    exactAgreementFlag6543 = shearedAgreementFlag := by
  rw [shearedAgreementFlag_value]
  rfl

/-- Generic exact-pole existence specialized abstractly to a flag support;
keeping the flag parameter opaque avoids reducing its potentially huge
finite lattice support during elaboration. -/
theorem exists_genericExactPolePolynomial_flagSupport
    (hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 2))
    (hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1)
    (p : FlagDegree) :
    Nonempty (GenericExactPolePolynomial G T H (flagSupport p) 2
      hseparator hproj) :=
  exists_genericExactPolePolynomial hseparator hproj (flagSupport p)
    (flagSupport_downwardClosed p) (zero_mem_flagSupport p)

/-- Rational-function evaluation depends only on the chosen field element;
the transcendence proof is propositionally irrelevant. -/
theorem elementEmbedding_congr
    {L : Type} [Field L] [Algebra Omega L]
    {s t : L} (hs : Transcendental Omega s)
    (ht : Transcendental Omega t) (h : s = t) :
    elementEmbedding Omega L s hs = elementEmbedding Omega L t ht := by
  subst t
  rfl

/-- The arbitrary-element embedding specializes definitionally to the
existing coordinate rational-base embedding. -/
theorem elementEmbedding_coordinate_eq_rationalBaseEmbedding
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (i : Fin 3) (hs ht : Transcendental Omega (coordinate Omega P i)) :
    elementEmbedding Omega (CoordinateField Omega P)
        (coordinate Omega P i) hs =
      rationalBaseEmbedding Omega P i ht := by
  rfl

/-- The sole residual premise after common avoidance and trapezoid support
arithmetic: the chosen outer variable really occurs in the transformed
irreducible surface relation. -/
structure FlagProjectionPositivity
    (D : NestedFlagProjectionData hseparator hproj)
    (G : MvPolynomial (Fin 3) Omega) : Prop where
  u : 0 < (planeMap Omega uOrder
    (flagAlgHom D.lam D.mu (D.mu * D.lam) G)).natDegree
  v : 0 < (planeMap Omega vOrder
    (flagAlgHom D.lam D.mu (D.mu * D.lam) G)).natDegree
  z : 0 < (planeMap Omega zOrder
    (flagAlgHom D.lam D.mu (D.mu * D.lam) G)).natDegree

theorem unitZ_polynomial_pole
    (B : GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
      hseparator hproj)
    (C : RegularComponent Omega G T H)
    (v : Place Omega (CoordinateField Omega C.1)) :
    let b := MvPolynomial.eval₂Hom
      (algebraMap Omega (CoordinateField Omega C.1))
      (coordinate Omega C.1) B.polynomial
    poleOrder v.val b = poleOrder v.val (coordinate Omega C.1 2) := by
  dsimp only
  calc
    poleOrder v.val
        (MvPolynomial.eval₂Hom
          (algebraMap Omega (CoordinateField Omega C.1))
          (coordinate Omega C.1) B.polynomial) =
        exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport unitZFlag) := B.exact_pole C v
    _ = poleOrder v.val (coordinate Omega C.1 2) :=
      exponentSetPoleWeight_unitZ v.val (coordinate Omega C.1)

theorem unitYZ_polynomial_pole
    (D : NestedFlagProjectionData hseparator hproj)
    (B : GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
      hseparator hproj)
    (C : RegularComponent Omega G T H)
    (v : Place Omega (CoordinateField Omega C.1)) :
    let b := MvPolynomial.eval₂Hom
      (algebraMap Omega (CoordinateField Omega C.1))
      (coordinate Omega C.1) B.polynomial
    poleOrder v.val b = poleOrder v.val (affineU Omega C.1 D.lam) := by
  dsimp only
  calc
    poleOrder v.val
        (MvPolynomial.eval₂Hom
          (algebraMap Omega (CoordinateField Omega C.1))
          (coordinate Omega C.1) B.polynomial) =
        exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport unitYZFlag) := B.exact_pole C v
    _ = max (poleOrder v.val (coordinate Omega C.1 0))
          (poleOrder v.val (coordinate Omega C.1 2)) :=
      exponentSetPoleWeight_unitYZ v.val (coordinate Omega C.1)
    _ = poleOrder v.val (affineU Omega C.1 D.lam) :=
      (nested_u_pole D C v).symm

theorem unitAll_polynomial_pole
    (D : NestedFlagProjectionData hseparator hproj)
    (B : GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
      hseparator hproj)
    (C : RegularComponent Omega G T H)
    (v : Place Omega (CoordinateField Omega C.1)) :
    let b := MvPolynomial.eval₂Hom
      (algebraMap Omega (CoordinateField Omega C.1))
      (coordinate Omega C.1) B.polynomial
    poleOrder v.val b =
      poleOrder v.val (affineV Omega C.1 D.mu (D.mu * D.lam)) := by
  dsimp only
  calc
    poleOrder v.val
        (MvPolynomial.eval₂Hom
          (algebraMap Omega (CoordinateField Omega C.1))
          (coordinate Omega C.1) B.polynomial) =
        exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport unitAllFlag) := B.exact_pole C v
    _ = max (poleOrder v.val (coordinate Omega C.1 1))
          (max (poleOrder v.val (coordinate Omega C.1 0))
            (poleOrder v.val (coordinate Omega C.1 2))) :=
      exponentSetPoleWeight_unitAll v.val (coordinate Omega C.1)
    _ = poleOrder v.val
          (affineV Omega C.1 D.mu (D.mu * D.lam)) :=
      (nested_v_pole D C v).symm

/-- The three exact unit-support principal-cycle budgets, with their numeric
65.43 caps, assembled from ordinary trapezoid resultants. -/
def flagProjectionCycleBudget6543_of_nested
    (D : NestedFlagProjectionData hseparator hproj)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport shearedSurfaceFlag)
    (hTsupport : T.support ⊆ flagSupport shearedAgreementFlag)
    (hpositive : FlagProjectionPositivity D G)
    (B : GenericExactPolePolynomial G T H
      (flagSupport shearedAgreementFlag) 2 hseparator hproj)
    (BZ : GenericExactPolePolynomial G T H
      (flagSupport unitZFlag) 2 hseparator hproj)
    (BYZ : GenericExactPolePolynomial G T H
      (flagSupport unitYZFlag) 2 hseparator hproj)
    (BAll : GenericExactPolePolynomial G T H
      (flagSupport unitAllFlag) 2 hseparator hproj) :
    FlagProjectionCycleBudget shearedAgreementFlag 2 hseparator hproj B
      flagZMixedCap flagYZMixedCap flagAllMixedCap := by
  let lam := D.lam
  let mu := D.mu
  let nu := D.mu * D.lam
  let gCaps := flagTrapezoidCaps_flagAlgHom shearedSurfaceFlag G
    lam mu nu hGsupport
  let tCaps := flagTrapezoidCaps_flagAlgHom shearedAgreementFlag T
    lam mu nu hTsupport
  let htZ : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0))) := by
    intro C
    simpa [zOrder, Equiv.swap_apply_def, lam, mu, nu] using hseparator C
  let htU : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0))) := by
    intro C
    simpa [uOrder, lam, mu, nu] using D.hU C
  let htV : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0))) := by
    intro C
    simpa [vOrder, Equiv.swap_apply_def, lam, mu, nu] using hAffineV D C
  have hembZ (C : RegularComponent Omega G T H) :
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0)))
          (htZ C) =
        elementEmbedding Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 2) (hseparator C) :=
    elementEmbedding_congr (htZ C) (hseparator C)
      (by simp [zOrder, Equiv.swap_apply_def, lam, mu, nu])
  have hembU (C : RegularComponent Omega G T H) :
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0)))
          (htU C) =
        elementEmbedding Omega (CoordinateField Omega C.1)
          (affineU Omega C.1 D.lam) (D.hU C) :=
    elementEmbedding_congr (htU C) (D.hU C)
      (by simp [uOrder, lam, mu, nu])
  have hembV (C : RegularComponent Omega G T H) :
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0)))
          (htV C) =
        elementEmbedding Omega (CoordinateField Omega C.1)
          (affineV Omega C.1 D.mu (D.mu * D.lam)) (hAffineV D C) :=
    elementEmbedding_congr (htV C) (hAffineV D C)
      (by simp [vOrder, Equiv.swap_apply_def, lam, mu, nu])
  have hTne : T ≠ 0 := by
    intro hzero
    apply hproper
    rw [hzero]
    exact dvd_zero G
  let zBudget : PrincipalCycleBudget (flagSupport unitZFlag) 2
      hseparator hproj BZ flagZMixedCap :=
    principalCycleBudget_of_flag_trapezoid BZ lam mu nu zOrder
      htZ
      (by
        intro C
        rw [hembZ C]
        simpa [zOrder, Equiv.swap_apply_def, lam, mu, nu] using
          flag_generators_z Omega C.1 lam mu nu (hseparator C))
      (by
        intro C
        rw [hembZ C,
          elementEmbedding_coordinate_eq_rationalBaseEmbedding C.1 2
            (hseparator C) (hseparator C)]
        exact (hproj C 2 (hseparator C)).2)
      (by intro C v; simpa [zOrder, Equiv.swap_apply_def, lam, mu, nu,
          CoordinatePoleMass.poleOrder] using
        unitZ_polynomial_pole BZ C v)
      hG hproper hpositive.z 5 1179639 26 6684622 flagZMixedCap hTne
      (by simpa [gCaps, shearedSurfaceFlag] using gCaps.zOuter)
      (by simpa [tCaps, shearedAgreementFlag_value] using tCaps.zOuter)
      (by simpa [gCaps, shearedSurfaceFlag] using gCaps.zTotal)
      (by simpa [tCaps, shearedAgreementFlag_value] using tCaps.zTotal)
      ContactFlagTrapezoidCaps6543Research.z_trapezoid_budget6543
  let yzBudget : PrincipalCycleBudget (flagSupport unitYZFlag) 2
      hseparator hproj BYZ flagYZMixedCap :=
    principalCycleBudget_of_flag_trapezoid BYZ lam mu nu uOrder
      htU
      (by
        intro C
        rw [hembU C]
        simpa [uOrder, lam, mu, nu] using
          flag_generators_u Omega C.1 lam mu nu (D.hU C))
      (by
        intro C
        rw [hembU C]
        exact D.separableU C)
      (by intro C v; simpa [uOrder, lam, mu, nu,
          CoordinatePoleMass.poleOrder] using
        unitYZ_polynomial_pole D BYZ C v)
      hG hproper hpositive.u 5 1179639 376 98434322 flagYZMixedCap hTne
      (by simpa [gCaps, shearedSurfaceFlag] using gCaps.uOuter)
      (by simpa [tCaps, shearedAgreementFlag_value] using tCaps.uOuter)
      (by simpa [gCaps, shearedSurfaceFlag] using gCaps.uTotal)
      (by simpa [tCaps, shearedAgreementFlag_value] using tCaps.uTotal)
      ContactFlagTrapezoidCaps6543Research.u_trapezoid_budget6543
  let allBudget : PrincipalCycleBudget (flagSupport unitAllFlag) 2
      hseparator hproj BAll flagAllMixedCap :=
    principalCycleBudget_of_flag_trapezoid BAll lam mu nu vOrder
      htV
      (by
        intro C
        rw [hembV C]
        simpa [vOrder, Equiv.swap_apply_def, lam, mu, nu] using
          flag_generators_v Omega C.1 lam mu nu (hAffineV D C))
      (by
        intro C
        rw [hembV C]
        exact separableAffineV D C)
      (by intro C v; simpa [vOrder, Equiv.swap_apply_def, lam, mu, nu,
          CoordinatePoleMass.poleOrder] using
        unitAll_polynomial_pole D BAll C v)
      hG hproper hpositive.v 26 6684622 376 98434322 flagAllMixedCap hTne
      (by simpa [gCaps, shearedSurfaceFlag] using gCaps.vOuter)
      (by simpa [tCaps, shearedAgreementFlag_value] using tCaps.vOuter)
      (by simpa [gCaps, shearedSurfaceFlag] using gCaps.vTotal)
      (by simpa [tCaps, shearedAgreementFlag_value] using tCaps.vTotal)
      ContactFlagTrapezoidCaps6543Research.v_trapezoid_budget6543
  exact FlagProjectionCycleBudget.ofNestedProjectionBudgets B BZ BYZ BAll
    zBudget yzBudget allBudget

/-- End-to-end geometric provider consumed by the already-green 65.43
whole-surface and protocol chain.  All support, pole, separability, and
resultant arithmetic is internal; only transformed outer-degree positivity
remains explicit. -/
def residualComponentBudget6543_of_nested
    (D : NestedFlagProjectionData hseparator hproj)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport shearedSurfaceFlag)
    (hTsupport : T.support ⊆ flagSupport shearedAgreementFlag)
    (hpositive : FlagProjectionPositivity D G)
    (B : GenericExactPolePolynomial G T H
      (flagSupport shearedAgreementFlag) 2 hseparator hproj)
    (BZ : GenericExactPolePolynomial G T H
      (flagSupport unitZFlag) 2 hseparator hproj)
    (BYZ : GenericExactPolePolynomial G T H
      (flagSupport unitYZFlag) 2 hseparator hproj)
    (BAll : GenericExactPolePolynomial G T H
      (flagSupport unitAllFlag) 2 hseparator hproj) :
    ResidualComponentBudget G T H
      (fun A ↦ A.support ⊆ flagSupport shearedAgreementFlag)
      flagWholeMixedCap :=
  (flagProjectionCycleBudget6543_of_nested D hG hproper hGsupport hTsupport
    hpositive B BZ BYZ BAll).toResidualComponentBudget6543

/-- The shortest exact 65.43 geometric seam: it is enough to exhibit one
common nested projection with positive outer degree in the three ordinary
resultant presentations.  All four exact-pole polynomials are then obtained
by dependent genericity inside this theorem. -/
theorem exists_residualComponentBudget6543_of_projectionPositivity
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport shearedSurfaceFlag)
    (hTsupport : T.support ⊆ flagSupport shearedAgreementFlag)
    (hpositive : ∃ D : NestedFlagProjectionData hseparator hproj,
      FlagProjectionPositivity D G) :
    Nonempty (ResidualComponentBudget G T H
      (fun A ↦ A.support ⊆ flagSupport shearedAgreementFlag)
      flagWholeMixedCap) := by
  obtain ⟨D, hD⟩ := hpositive
  obtain ⟨B⟩ := exists_genericExactPolePolynomial_flagSupport
    hseparator hproj exactAgreementFlag6543
  rw [exactAgreementFlag6543_eq] at B
  obtain ⟨BZ⟩ := exists_genericExactPolePolynomial_flagSupport
    hseparator hproj unitZFlag
  obtain ⟨BYZ⟩ := exists_genericExactPolePolynomial_flagSupport
    hseparator hproj unitYZFlag
  obtain ⟨BAll⟩ := exists_genericExactPolePolynomial_flagSupport
    hseparator hproj unitAllFlag
  exact ⟨residualComponentBudget6543_of_nested D hG hproper hGsupport
    hTsupport hD B BZ BYZ BAll⟩

end

end ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles6543Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles6543Research.flagProjectionCycleBudget6543_of_nested

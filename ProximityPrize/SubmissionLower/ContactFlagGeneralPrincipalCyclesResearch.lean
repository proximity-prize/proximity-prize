import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles6543Research
import ProximityPrize.SubmissionLower.ContactFlagSymbolicTrapezoidResearch
namespace ProximityPrize.SubmissionLower.ContactFlagGeneralPrincipalCyclesResearch
open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactLocalPoleBound ContactDependentGenericity6543Research
open ContactFlagBezout6543Research ContactFlagPoleInequality6543Research
open ContactFlagTriangularProjectionResearch
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagExactSeparableProjection6543Research
open ContactFlagGlobalPoleProjection6543Research
open ContactFlagPrincipalCycleAdapter6543Research
open ContactFlagProjectionProvider6543Research
open ContactFlagTrapezoidCaps6543Research
open ContactFlagPrincipalCycles6543Research
open ContactFlagSymbolicTrapezoidResearch
open ContactResidualSparseComponentAdapterResearch
open TrivariateRationalCollection ActualPlaneCoordinateKernel
  ArbitraryRationalProjectionResearch
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {hseparator:∀ C:RegularComponent Omega G T H,
  Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj:∀ C:RegularComponent Omega G T H,
  ProjectionsFiniteSeparable Omega C.1}
def flagProjectionCycleBudget_of_nested_general
    (p q r:FlagDegree)
    (D:NestedFlagProjectionData hseparator hproj)
    (hG:Irreducible G) (hproper:¬ G∣T)
    (hGsupport:G.support ⊆ flagSupport p)
    (hTsupport:T.support ⊆ flagSupport q)
    (hpositive:FlagProjectionPositivity D G)
    (B:GenericExactPolePolynomial G T H (flagSupport r) 2
      hseparator hproj)
    (BZ:GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
      hseparator hproj)
    (BYZ:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
      hseparator hproj)
    (BAll:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
      hseparator hproj):
    FlagProjectionCycleBudget r 2 hseparator hproj B
      (flagMixed p q unitZFlag)
      (flagMixed p q unitYZFlag)
      (flagMixed p q unitAllFlag):=by
  let lam:=D.lam
  let mu:=D.mu
  let nu:=D.mu*D.lam
  let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
  let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
  let htZ:∀ C:RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0))):=by
    intro C
    simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using hseparator C
  let htU:∀ C:RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0))):=by
    intro C
    simpa [uOrder,lam,mu,nu] using D.hU C
  let htV:∀ C:RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0))):=by
    intro C
    simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using hAffineV D C
  have hembZ (C:RegularComponent Omega G T H):
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0)))
          (htZ C)=
        elementEmbedding Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 2) (hseparator C):=
    elementEmbedding_congr (htZ C) (hseparator C)
      (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
  have hembU (C:RegularComponent Omega G T H):
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0)))
          (htU C)=
        elementEmbedding Omega (CoordinateField Omega C.1)
          (affineU Omega C.1 D.lam) (D.hU C):=
    elementEmbedding_congr (htU C) (D.hU C)
      (by simp [uOrder,lam,mu,nu])
  have hembV (C:RegularComponent Omega G T H):
      elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0)))
          (htV C)=
        elementEmbedding Omega (CoordinateField Omega C.1)
          (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C):=
    elementEmbedding_congr (htV C) (hAffineV D C)
      (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
  have hTne:T≠0:=by
    intro hzero
    apply hproper
    rw [hzero]
    exact dvd_zero G
  let zBudget:PrincipalCycleBudget (flagSupport unitZFlag) 2
      hseparator hproj BZ (flagMixed p q unitZFlag):=
    principalCycleBudget_of_flag_trapezoid BZ lam mu nu zOrder htZ
      (by
        intro C
        rw [hembZ C]
        simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
          flag_generators_z Omega C.1 lam mu nu (hseparator C))
      (by
        intro C
        rw [hembZ C,
          elementEmbedding_coordinate_eq_rationalBaseEmbedding C.1 2
            (hseparator C) (hseparator C)]
        exact (hproj C 2 (hseparator C)).2)
      (by
        intro C v
        simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu,
          CoordinatePoleMass.poleOrder] using
          unitZ_polynomial_pole BZ C v)
      hG hproper hpositive.z p.all q.all (p.yz+p.all)
      (q.yz+q.all) (flagMixed p q unitZFlag) hTne
      (by simpa only [gCaps] using gCaps.zOuter)
      (by simpa only [tCaps] using tCaps.zOuter)
      (by simpa only [gCaps] using gCaps.zTotal)
      (by simpa only [tCaps] using tCaps.zTotal)
      (z_flag_trapezoid_budget p q)
  let yzBudget:PrincipalCycleBudget (flagSupport unitYZFlag) 2
      hseparator hproj BYZ (flagMixed p q unitYZFlag):=
    principalCycleBudget_of_flag_trapezoid BYZ lam mu nu uOrder htU
      (by
        intro C
        rw [hembU C]
        simpa [uOrder,lam,mu,nu] using
          flag_generators_u Omega C.1 lam mu nu (D.hU C))
      (by
        intro C
        rw [hembU C]
        exact D.separableU C)
      (by
        intro C v
        simpa [uOrder,lam,mu,nu,CoordinatePoleMass.poleOrder] using
          unitYZ_polynomial_pole D BYZ C v)
      hG hproper hpositive.u p.all q.all
      (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
      (flagMixed p q unitYZFlag) hTne
      (by simpa only [gCaps] using gCaps.uOuter)
      (by simpa only [tCaps] using tCaps.uOuter)
      (by simpa only [gCaps] using gCaps.uTotal)
      (by simpa only [tCaps] using tCaps.uTotal)
      (u_flag_trapezoid_budget p q)
  let allBudget:PrincipalCycleBudget (flagSupport unitAllFlag) 2
      hseparator hproj BAll (flagMixed p q unitAllFlag):=
    principalCycleBudget_of_flag_trapezoid BAll lam mu nu vOrder htV
      (by
        intro C
        rw [hembV C]
        simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
          flag_generators_v Omega C.1 lam mu nu (hAffineV D C))
      (by
        intro C
        rw [hembV C]
        exact separableAffineV D C)
      (by
        intro C v
        simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu,
          CoordinatePoleMass.poleOrder] using
          unitAll_polynomial_pole D BAll C v)
      hG hproper hpositive.v (p.yz+p.all) (q.yz+q.all)
      (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
      (flagMixed p q unitAllFlag) hTne
      (by simpa only [gCaps] using gCaps.vOuter)
      (by simpa only [tCaps] using tCaps.vOuter)
      (by simpa only [gCaps] using gCaps.vTotal)
      (by simpa only [tCaps] using tCaps.vTotal)
      (v_flag_trapezoid_budget p q)
  exact FlagProjectionCycleBudget.ofNestedProjectionBudgets
    B BZ BYZ BAll zBudget yzBudget allBudget
def residualComponentBudget_flagMixed_of_nested
    (p q r:FlagDegree)
    (D:NestedFlagProjectionData hseparator hproj)
    (hG:Irreducible G) (hproper:¬ G∣T)
    (hGsupport:G.support ⊆ flagSupport p)
    (hTsupport:T.support ⊆ flagSupport q)
    (hpositive:FlagProjectionPositivity D G)
    (B:GenericExactPolePolynomial G T H (flagSupport r) 2
      hseparator hproj)
    (BZ:GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
      hseparator hproj)
    (BYZ:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
      hseparator hproj)
    (BAll:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
      hseparator hproj):
    ResidualComponentBudget G T H
      (fun A↦A.support ⊆ flagSupport r) (flagMixed p q r):=by
  rw [flagMixed_projection_decomposition]
  exact (flagProjectionCycleBudget_of_nested_general p q r D hG hproper
    hGsupport hTsupport hpositive B BZ BYZ BAll).toResidualComponentBudget
theorem exists_residualComponentBudget_flagMixed_of_projectionPositivity
    (p q r:FlagDegree)
    (hG:Irreducible G) (hproper:¬ G∣T)
    (hGsupport:G.support ⊆ flagSupport p)
    (hTsupport:T.support ⊆ flagSupport q)
    (hpositive:∃ D:NestedFlagProjectionData hseparator hproj,
      FlagProjectionPositivity D G):
    Nonempty (ResidualComponentBudget G T H
      (fun A↦A.support ⊆ flagSupport r) (flagMixed p q r)):=by
  obtain ⟨D,hD⟩:=hpositive
  obtain ⟨B⟩:=exists_genericExactPolePolynomial_flagSupport
    hseparator hproj r
  obtain ⟨BZ⟩:=exists_genericExactPolePolynomial_flagSupport
    hseparator hproj unitZFlag
  obtain ⟨BYZ⟩:=exists_genericExactPolePolynomial_flagSupport
    hseparator hproj unitYZFlag
  obtain ⟨BAll⟩:=exists_genericExactPolePolynomial_flagSupport
    hseparator hproj unitAllFlag
  exact ⟨residualComponentBudget_flagMixed_of_nested p q r D hG hproper
    hGsupport hTsupport hD B BZ BYZ BAll⟩
end
end ProximityPrize.SubmissionLower.ContactFlagGeneralPrincipalCyclesResearch

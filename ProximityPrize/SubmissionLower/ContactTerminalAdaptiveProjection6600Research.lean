import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research
import ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
import ProximityPrize.SubmissionLower.ContactParameters6600Research
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
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem degree_bounds_of_polynomialInFlag
    {p:FlagDegree} {F:MvPolynomial (Fin 3) Omega}
    (hF:PolynomialInFlag p F):
    F.degreeOf 0 ≤ p.yz+p.all∧
      F.degreeOf 1 ≤ p.all∧
      F.degreeOf 2 ≤ p.zOnly+p.yz+p.all:=by
  refine ⟨?_,?_,?_⟩
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (hF e he).1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_left (e 2) (e 0+e 1)).trans (by
      simpa only [Nat.add_assoc] using (hF e he).2.2)
theorem terminalAdaptiveProjectionFamilies_of_rectangular_caps
    [CharP Omega prime]
    {flag:FlagDegree}
    (S:ResidualStage phi Gamma x prime errors flag w)
    (hflagZ:flag.zOnly ≤ 495)
    (hflagY:flag.yz ≤ 43)
    (hflagS:flag.all ≤ 8):
    TerminalAdaptiveProjectionFamilies S:=by
  classical
  intro D i hi hproper
  let T:=agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let H:=regularitySurface phi D.stage.F
  have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
  have hTflag:PolynomialInFlag (residualAgreementFlag D.degree) T:=by
    exact surfaceMap_agreement_in_flag_of_surface_weights
      D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j↦(j.factorial:K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  obtain ⟨hGY,hGS,hGZ⟩:=degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY,hTS,hTZ⟩:=degree_bounds_of_polynomialInFlag hTflag
  have hD:D.degree ≤ w:=D.degree_le.trans (Nat.le_refl w)
  have hGY':D.stage.G.degreeOf 0 ≤ 51:=by omega
  have hGS':D.stage.G.degreeOf 1 ≤ 8:=by omega
  have hGZ':D.stage.G.degreeOf 2 ≤ 546:=by omega
  have hTY':T.degreeOf 0 ≤ 1+85*w:=by
    dsimp only [residualAgreementFlag] at hTY
    omega
  have hTS':T.degreeOf 1 ≤ 15*w:=by
    dsimp only [residualAgreementFlag] at hTS
    omega
  have hTZ':T.degreeOf 2 ≤ 1+1005*w:=by
    dsimp only [residualAgreementFlag] at hTZ
    omega
  have hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < prime:=by
    intro j
    fin_cases j
    · exact hGY'.trans_lt (by norm_num [prime])
    · exact hGS'.trans_lt (by norm_num [prime])
    · exact hGZ'.trans_lt (by norm_num [prime])
  have hmixedY:
      coordinateMixedDegree Omega D.stage.G T 0 < prime:=by
    rw [coordinateMixedDegree_zero]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTS' hGZ')
      (Nat.mul_le_mul hGS' hTZ')).trans_lt
    norm_num [w,prime]
  have hmixedZ:
      coordinateMixedDegree Omega D.stage.G T 2 < prime:=by
    rw [coordinateMixedDegree_two]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt
    norm_num [w,prime]
  let hY:∀ C:RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 0:=by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 0 htr
      prime D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproper hGdegree hmixedY
  let hZ:∀ C:RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 2:=by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      prime D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproper hGdegree hmixedZ
  have hbase:∀ C:RegularComponent Omega D.stage.G T H,
      Nonempty (SeparableLiteralCoordinate C.1):=by
    intro C
    exact exists_separableLiteralCoordinate_of_YZ_gates C.1
      (regularComponent_ne_point Omega D.stage.G T H C) (hY C) (hZ C)
  let base:∀ C:RegularComponent Omega D.stage.G T H,
      SeparableLiteralCoordinate C.1:=fun C↦Classical.choice (hbase C)
  refine ⟨base,?_⟩
  exact exists_adaptiveUnitProjectionFamily_of_nested flag
    (residualAgreementFlag D.degree) base hY hZ
    (residualStage_pderiv_one_ne_zero D.stage)
    D.stage.irreducible_G hproper
    ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
    ((support_subset_flagSupport_iff (residualAgreementFlag D.degree) T).2 hTflag)
end
end ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactFactorCaps

/-!
# Parameterized residual support and agreement flags

This module isolates the smallest parameter-generic core needed to retarget
the accepted residual-stage development.  A residual surface stores three
preserved weights:

* pure `R` weight;
* joint `Y+R` weight;
* total `Y+R+Z` weight.

The accepted stage freezes these caps to `(8,43,503)`.  The recursive-GCD
fixed meet needs `(6,34,604)`.  The affine residual transform and the
Minkowski agreement recurrence are already generic, so the definitions and
proofs below merely package those low-level theorems with explicit caps.

The resulting `ResidualSupportData` is intended to replace the three literal
support fields of both `ResidualStage` and `CurveResidualStage`.  Its
`globalResidual` theorem supplies the fields of a residual successor, while
`surfaceMap_globalResidual_agreement_in_flag` supplies every induced cut flag
used by the terminal and factor providers.

## Deliberate boundary

This module does not introduce a parallel residual-stage hierarchy.  The
existing `ResidualStage`, `CurveResidualStage`, their step relations,
reachability closures, terminal descendants, component families, and factor
providers are indexed by the frozen structures.  Retargeting them in a new
file would copy broad proof bodies.  The non-duplicating migration is:

1. add a support-parameter index to the two accepted stage structures and
   replace their three support fields by `ResidualSupportData`;
2. thread the same index through steps, reachability, and descendants, using
   `ResidualSupportData.globalResidual` in both successor constructors;
3. replace `residualAgreementFlag d` by
   `support.residualAgreementFlag d` in incidence and terminal APIs;
4. retain the accepted profile through `acceptedSupport`, and instantiate the
   fixed meet through `fixedMeetSupport`.

No identity, incidence, component, or projection geometry changes at that
seam.
-/

namespace ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch

open ContactGenericSurface ContactTaylorNumerators
open ContactInterpolation ContactFactorCaps
open ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactFlagBezout6543Research

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- The three support caps preserved by global actual-identity
residualization.  The order assumptions make the nested flag differences
literal natural numbers; `two_le_ys` is the exact Minkowski recurrence gate.
-/
structure ResidualSupportParameters where
  s : ℕ
  ys : ℕ
  total : ℕ
  one_le_s : 1 ≤ s
  s_le_ys : s ≤ ys
  ys_le_total : ys ≤ total
  two_le_ys : 2 ≤ ys
  deriving DecidableEq

namespace ResidualSupportParameters

/-- The degree direction of an agreement cut, in nested
`(Z-only,YZ,all)` coordinates. -/
def agreementDirection (P : ResidualSupportParameters) : FlagDegree :=
  ⟨2 * (P.total - P.ys), 2 * (P.ys - P.s), 2 * P.s - 1⟩

/-- The exact affine agreement flag at residual degree `d`.  The unit is in
the `YZ` coordinate, matching the accepted score-66 flag. -/
def residualAgreementFlag (P : ResidualSupportParameters) (d : ℕ) : FlagDegree :=
  ⟨P.agreementDirection.zOnly * d,
    1 + P.agreementDirection.yz * d,
    P.agreementDirection.all * d⟩

theorem agreementDirection_values (P : ResidualSupportParameters) :
    P.agreementDirection =
      ⟨2 * (P.total - P.ys), 2 * (P.ys - P.s), 2 * P.s - 1⟩ := rfl

theorem residualAgreementFlag_ys (P : ResidualSupportParameters) (d : ℕ) :
    (P.residualAgreementFlag d).yz + (P.residualAgreementFlag d).all =
      1 + d * (2 * P.ys - 1) := by
  have hcoeff : 2 * (P.ys - P.s) + (2 * P.s - 1) = 2 * P.ys - 1 := by
    rw [Nat.mul_sub_left_distrib]
    have hle := Nat.mul_le_mul_left 2 P.s_le_ys
    have hpos := P.one_le_s
    omega
  simp only [residualAgreementFlag, agreementDirection]
  rw [← hcoeff]
  ring

theorem residualAgreementFlag_total (P : ResidualSupportParameters) (d : ℕ) :
    (P.residualAgreementFlag d).zOnly +
        (P.residualAgreementFlag d).yz +
        (P.residualAgreementFlag d).all =
      1 + d * (2 * P.total - 1) := by
  have hcoeff : 2 * (P.total - P.ys) + 2 * (P.ys - P.s) +
      (2 * P.s - 1) = 2 * P.total - 1 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    have hle₁ := Nat.mul_le_mul_left 2 P.s_le_ys
    have hle₂ := Nat.mul_le_mul_left 2 P.ys_le_total
    have hpos := P.one_le_s
    omega
  simp only [residualAgreementFlag, agreementDirection]
  rw [← hcoeff]
  ring

/-- The accepted promoted score-66.18 support profile. -/
def acceptedSupport : ResidualSupportParameters where
  s := 8
  ys := 43
  total := 503
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

/-- The recursive-GCD fixed meet support profile. -/
def fixedMeetSupport : ResidualSupportParameters where
  s := 6
  ys := 34
  total := 604
  one_le_s := by norm_num
  s_le_ys := by norm_num
  ys_le_total := by norm_num
  two_le_ys := by norm_num

theorem accepted_agreement_flag (d : ℕ) :
    acceptedSupport.residualAgreementFlag d =
      ContactIdentityResidualGlobalFlagResearch.residualAgreementFlag d := by
  rfl

theorem fixedMeet_agreement_direction :
    fixedMeetSupport.agreementDirection = ⟨1140, 56, 11⟩ := by
  norm_num [fixedMeetSupport, agreementDirection]

theorem fixedMeet_agreement_flag (d : ℕ) :
    fixedMeetSupport.residualAgreementFlag d =
      ⟨1140 * d, 1 + 56 * d, 11 * d⟩ := by
  rfl

end ResidualSupportParameters

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-- The parameterized replacement for the three frozen support proof fields
of a residual stage. -/
structure ResidualSupportData (P : ResidualSupportParameters) (F : Poly4 K) : Prop where
  s_weight : wt residualSWeights F ≤ P.s
  ys_weight : wt residualYSWeights F ≤ P.ys
  total_weight : wt residualTotalWeights F ≤ P.total

namespace ResidualSupportData

/-- The final recursive-GCD meet box supplies its initial parameterized
support state directly. -/
theorem fixedMeet_of_mem_box
    (F : Poly4 K)
    (hbox : F ∈ globalCoefficientBox K 4570175 131071 598 6) :
    ResidualSupportData ResidualSupportParameters.fixedMeetSupport F := by
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights F 6).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 598 ∧ d 2 ≤ 6 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 4570175 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 6
    norm_num
    exact hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights F 34).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 598 ∧ d 2 ≤ 6 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 4570175 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 34
    norm_num
    norm_num at hb
    omega
  · apply (weightedTotalDegree_le_iff residualTotalWeights F 604).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 598 ∧ d 2 ≤ 6 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 4570175 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 604
    norm_num
    norm_num at hb
    omega

/-- Global actual-identity residualization preserves an arbitrary supplied
support triple. -/
theorem globalResidual
    {P : ResidualSupportParameters} {F : Poly4 K}
    (H : ResidualSupportData P F)
    (P0 P1 V : Polynomial K) :
    ResidualSupportData P (globalResidualHom P0 P1 V F) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_s] using H.s_weight)
  · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_ys] using H.ys_weight)
  · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
      P0 P1 V F).trans (by
        simpa [residualPullWeights_total] using H.total_weight)

/-- Coordinate degree consequences used by the generic agreement recurrence.
-/
theorem coordinate_bounds
    {P : ResidualSupportParameters} {F : Poly4 K}
    (H : ResidualSupportData P F) :
    F.degreeOf (1 : Fin 4) ≤ P.ys ∧
      F.degreeOf (2 : Fin 4) ≤ P.s ∧
      F.degreeOf (3 : Fin 4) ≤ P.total := by
  have hR : F.degreeOf (2 : Fin 4) ≤ P.s := by
    have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> rfl
    have hs := H.s_weight
    rw [hw, wt, MvPolynomial.weightedTotalDegree_piSingle] at hs
    exact hs
  have hY : F.degreeOf (1 : Fin 4) ≤ P.ys := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans
      H.ys_weight
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ P.ys at hw
    norm_num at hw
    omega
  have hZ : F.degreeOf (3 : Fin 4) ≤ P.total := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans
      H.total_weight
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ P.total at hw
    norm_num at hw
    omega
  exact ⟨hY, hR, hZ⟩

/-- Agreement weight bounds at arbitrary stored residual support caps. -/
theorem agreement_weight_bounds
    {P : ResidualSupportParameters} {F : Poly4 K}
    (H : ResidualSupportData P F)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    (agreementNumerator F d coeffs x u0 u1).degreeOf (2 : Fin 4) ≤
        d * (2 * P.s - 1) ∧
      wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
        1 + d * (2 * P.ys - 1) ∧
      wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
        1 + d * (2 * P.total - 1) := by
  obtain ⟨hY, hR, hZ⟩ := H.coordinate_bounds
  refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
    P.one_le_s hY hR hZ d coeffs x u0 u1).2.1, ?_, ?_⟩
  · have h := agreementNumerator_wt_le_minkowski residualYSWeights rfl
      F P.ys (by change 1 ≤ P.ys; exact P.one_le_s.trans P.s_le_ys)
      (by change 2 ≤ P.ys; exact P.two_le_ys)
      (by change 1 ≤ 1; norm_num) H.ys_weight d coeffs x u0 u1
    have hcoeff : P.ys + (P.ys - 1) = 2 * P.ys - 1 := by omega
    apply h.trans_eq
    change max 1 0 + d * (P.ys + (P.ys - 1)) =
      1 + d * (2 * P.ys - 1)
    rw [hcoeff]
    norm_num
  · have htotalTwo : 2 ≤ P.total := P.two_le_ys.trans P.ys_le_total
    have honeTotal : 1 ≤ P.total :=
      le_trans P.one_le_s (le_trans P.s_le_ys P.ys_le_total)
    have h := agreementNumerator_wt_le_minkowski residualTotalWeights rfl
      F P.total (by change 1 ≤ P.total; exact honeTotal)
      (by change 2 ≤ P.total; exact htotalTwo)
      (by change 1 ≤ 1; norm_num) H.total_weight d coeffs x u0 u1
    have hcoeff : P.total + (P.total - 1) = 2 * P.total - 1 := by omega
    apply h.trans_eq
    change max 1 1 + d * (P.total + (P.total - 1)) =
      1 + d * (2 * P.total - 1)
    rw [hcoeff]
    norm_num

/-- The mapped agreement cut belongs to the parameter-induced nested flag.
This is the direct replacement for the frozen
`surfaceMap_globalResidual_agreement_in_flag`. -/
theorem surfaceMap_agreement_in_flag
    {P : ResidualSupportParameters}
    (phi : Polynomial K →+* Omega) {F : Poly4 K}
    (H : ResidualSupportData P F)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (P.residualAgreementFlag d)
      (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
  obtain ⟨hR, hYS, hTotal⟩ := H.agreement_weight_bounds d coeffs x u0 u1
  have hqR := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hR
  have hqYS := (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
  have hqTotal :=
    (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTotal
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤
    1 + d * (2 * P.ys - 1) at hqYS
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤
    1 + d * (2 * P.total - 1) at hqTotal
  norm_num at hqYS hqTotal
  have hqR' : q 2 ≤ (P.residualAgreementFlag d).all := by
    change q 2 ≤ (2 * P.s - 1) * d
    rw [Nat.mul_comm]
    exact hqR
  change q 2 ≤ (P.residualAgreementFlag d).all ∧
    q 1 + q 2 ≤ (P.residualAgreementFlag d).yz +
      (P.residualAgreementFlag d).all ∧
    q 1 + q 2 + q 3 ≤ (P.residualAgreementFlag d).zOnly +
      (P.residualAgreementFlag d).yz +
      (P.residualAgreementFlag d).all
  refine ⟨hqR', ?_, ?_⟩
  · rw [P.residualAgreementFlag_ys]
    exact hqYS
  · rw [P.residualAgreementFlag_total]
    exact hqTotal

/-- Combined successor API: the support data is preserved and its agreement
cut receives the induced flag.  A parameterized residual-step constructor
can consume this pair directly without reproving support arithmetic. -/
theorem globalResidual_and_agreement_in_flag
    {P : ResidualSupportParameters} {F : Poly4 K}
    (H : ResidualSupportData P F)
    (phi : Polynomial K →+* Omega)
    (P0 P1 V : Polynomial K)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    let Fres := globalResidualHom P0 P1 V F
    ResidualSupportData P Fres ∧
      PolynomialInFlag (P.residualAgreementFlag d)
        (surfaceMap phi (agreementNumerator Fres d coeffs x u0 u1)) := by
  let Hres := H.globalResidual P0 P1 V
  exact ⟨Hres, Hres.surfaceMap_agreement_in_flag phi d coeffs x u0 u1⟩

end ResidualSupportData

end

end ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch

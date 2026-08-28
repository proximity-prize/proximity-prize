import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research
import ProximityPrize.SubmissionLower.TrivariateShearResearch

/-!
# Weighted Newton flags for the score-66 regular-factor family

The rectangular factor ledger charges independent maxima in `Y`, `R`, and
`Z`.  This file instead charges the three nested support functions
`R`, `Y+R`, and `Y+R+Z`.  Those support functions are additive across genuine
factor products, so the complete regular family fits the sharp surface flag
rather than the rectangular box.
-/

namespace ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research

open scoped BigOperators
open ContactParameters6600Research
open ContactInterpolation ContactGenericSurface ContactGeometricFactorCover
open ContactImplicitContactLift ContactFactorCaps ContactSingularDegreeBounds
open ContactFlagBezout6543Research
open ContactNearPencil6600FactorLedgerResearch
open ContactNearPencil6600FlagResearch
open ContactIdentityResidualGlobalFlagResearch

noncomputable section

variable {K L : Type} [Field K] [Field L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq L := Classical.decEq L

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

def swt (weights : Fin 3 → ℕ) (F : Poly3 K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights F

private theorem swt_s_le_ys (F : Poly3 K) :
    swt flagSWeights F ≤ swt flagYSWeights F := by
  unfold swt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  calc
    Finsupp.weight flagSWeights d ≤ Finsupp.weight flagYSWeights d := by
      rw [flag_weight_fin3, flag_weight_fin3]
      simp [flagSWeights, flagYSWeights]
    _ ≤ F.support.sup (Finsupp.weight flagYSWeights) :=
      MvPolynomial.le_weightedTotalDegree flagYSWeights hd

private theorem swt_ys_le_total (F : Poly3 K) :
    swt flagYSWeights F ≤ swt flagTotalWeights F := by
  unfold swt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  calc
    Finsupp.weight flagYSWeights d ≤ Finsupp.weight flagTotalWeights d := by
      rw [flag_weight_fin3, flag_weight_fin3]
      simp [flagYSWeights, flagTotalWeights]
    _ ≤ F.support.sup (Finsupp.weight flagTotalWeights) :=
      MvPolynomial.le_weightedTotalDegree flagTotalWeights hd

/-- Canonical nested flag obtained from the three Newton support functions. -/
def weightedFlag (F : Poly3 K) : FlagDegree :=
  let r := swt flagSWeights F
  let a := swt flagYSWeights F
  let t := swt flagTotalWeights F
  ⟨t - a, a - r, r⟩

/-- The canonical weighted flag contains the complete Newton support. -/
theorem polynomialIn_weightedFlag (F : Poly3 K) :
    PolynomialInFlag (weightedFlag F) F := by
  intro d hd
  have hr := MvPolynomial.le_weightedTotalDegree flagSWeights hd
  have ha := MvPolynomial.le_weightedTotalDegree flagYSWeights hd
  have ht := MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
  have hra := swt_s_le_ys F
  have hat := swt_ys_le_total F
  rw [flag_weight_fin3] at hr ha ht
  simp [flagSWeights, flagYSWeights, flagTotalWeights] at hr ha ht
  unfold swt at hra hat
  change d 1 ≤ MvPolynomial.weightedTotalDegree flagSWeights F ∧
    d 0 + d 1 ≤
      (MvPolynomial.weightedTotalDegree flagYSWeights F -
        MvPolynomial.weightedTotalDegree flagSWeights F) +
      MvPolynomial.weightedTotalDegree flagSWeights F ∧
    d 0 + d 1 + d 2 ≤
      (MvPolynomial.weightedTotalDegree flagTotalWeights F -
        MvPolynomial.weightedTotalDegree flagYSWeights F) +
        (MvPolynomial.weightedTotalDegree flagYSWeights F -
          MvPolynomial.weightedTotalDegree flagSWeights F) +
        MvPolynomial.weightedTotalDegree flagSWeights F
  simp only [flagSWeights, flagYSWeights, flagTotalWeights] at hra hat ⊢
  omega

private theorem weightedLift_ne_zero (weights : Fin 3 → ℕ) (F : Poly3 K)
    (hF : F ≠ 0) :
    TrivariateShearResearch.weightedLift (K := K) weights F ≠ 0 := by
  intro hzero
  apply hF
  apply TrivariateShearResearch.weightedLift_injective weights
  simpa only [map_zero] using hzero

private theorem swt_mul_eq (weights : Fin 3 → ℕ) (F G : Poly3 K)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    swt weights (F * G) = swt weights F + swt weights G := by
  unfold swt
  calc
    MvPolynomial.weightedTotalDegree weights (F * G) =
        (TrivariateShearResearch.weightedLift (K := K) weights
          (F * G)).degreeOf (3 : Fin 4) :=
      (TrivariateShearResearch.degree_weightedLift weights (F * G)).symm
    _ = (TrivariateShearResearch.weightedLift (K := K) weights F *
        TrivariateShearResearch.weightedLift (K := K) weights G).degreeOf
          (3 : Fin 4) := by rw [map_mul]
    _ = (TrivariateShearResearch.weightedLift (K := K) weights F).degreeOf
          (3 : Fin 4) +
        (TrivariateShearResearch.weightedLift (K := K) weights G).degreeOf
          (3 : Fin 4) :=
      MvPolynomial.degreeOf_mul_eq
        (weightedLift_ne_zero weights F hF)
        (weightedLift_ne_zero weights G hG)
    _ = MvPolynomial.weightedTotalDegree weights F +
        MvPolynomial.weightedTotalDegree weights G := by
      rw [TrivariateShearResearch.degree_weightedLift,
        TrivariateShearResearch.degree_weightedLift]

private theorem sum_swt_le_of_prod_dvd {ι : Type*} [DecidableEq ι]
    (weights : Fin 3 → ℕ) (I : Finset ι) (f : ι → Poly3 K) (Q : Poly3 K)
    (hQ : Q ≠ 0) (hdiv : (∏ i ∈ I, f i) ∣ Q) :
    (∑ i ∈ I, swt weights (f i)) ≤ swt weights Q := by
  classical
  have hprod : (∏ i ∈ I, f i) ≠ 0 := by
    intro hz
    obtain ⟨T, hT⟩ := hdiv
    exact hQ (by rw [hT, hz, zero_mul])
  have hf : ∀ i ∈ I, f i ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  have hsum : swt weights (∏ i ∈ I, f i) =
      ∑ i ∈ I, swt weights (f i) := by
    calc
      swt weights (∏ i ∈ I, f i) =
          (TrivariateShearResearch.weightedLift (K := K) weights
            (∏ i ∈ I, f i)).degreeOf (3 : Fin 4) :=
        (TrivariateShearResearch.degree_weightedLift weights _).symm
      _ = (∏ i ∈ I,
          TrivariateShearResearch.weightedLift (K := K) weights (f i)).degreeOf
            (3 : Fin 4) := by rw [map_prod]
      _ = ∑ i ∈ I,
          (TrivariateShearResearch.weightedLift (K := K) weights
            (f i)).degreeOf (3 : Fin 4) :=
        MvPolynomial.degreeOf_prod_eq I _ fun i hi ↦
          weightedLift_ne_zero weights (f i) (hf i hi)
      _ = ∑ i ∈ I, swt weights (f i) := by
        simp only [TrivariateShearResearch.degree_weightedLift, swt]
  rw [← hsum]
  obtain ⟨T, rfl⟩ := hdiv
  rw [swt_mul_eq weights (∏ i ∈ I, f i) T hprod
    (mul_ne_zero_iff.mp hQ).2]
  exact Nat.le_add_right _ _

/-- Weighted support functions add across the actual geometric factor family. -/
theorem surfaceFactors_swt_budget
    (weights : Fin 3 → ℕ) (phi : Polynomial K →+* L)
    (hphi : Function.Injective phi) (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g ∈ surfaceFactors phi F, swt weights g) ≤
      swt weights (surfaceMap phi F) := by
  exact sum_swt_le_of_prod_dvd weights (surfaceFactors phi F) id
    (surfaceMap phi F) (surfaceMap_ne_zero phi hphi F hF)
    (normalizedFactorSet_product_dvd _ (surfaceMap_ne_zero phi hphi F hF))

private theorem surfaceMap_swt_s_le
    (phi : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K) :
    swt flagSWeights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree residualSWeights F := by
  unfold swt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F he)
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  calc
    Finsupp.weight flagSWeights d.tail =
        Finsupp.weight residualSWeights d := by
      rw [flag_weight_fin3, ContactFactorCaps.weight_fin4]
      simp [flagSWeights, residualSWeights, Finsupp.tail_apply]
    _ ≤ F.support.sup (Finsupp.weight residualSWeights) := h

private theorem surfaceMap_swt_ys_le
    (phi : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K) :
    swt flagYSWeights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree residualYSWeights F := by
  unfold swt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F he)
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  calc
    Finsupp.weight flagYSWeights d.tail =
        Finsupp.weight residualYSWeights d := by
      rw [flag_weight_fin3, ContactFactorCaps.weight_fin4]
      simp [flagYSWeights, residualYSWeights, Finsupp.tail_apply]
    _ ≤ F.support.sup (Finsupp.weight residualYSWeights) := h

private theorem surfaceMap_swt_total_le
    (phi : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K) :
    swt flagTotalWeights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  unfold swt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F he)
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  calc
    Finsupp.weight flagTotalWeights d.tail =
        Finsupp.weight residualTotalWeights d := by
      rw [flag_weight_fin3, ContactFactorCaps.weight_fin4]
      simp [flagTotalWeights, residualTotalWeights, Finsupp.tail_apply]
    _ ≤ F.support.sup (Finsupp.weight residualTotalWeights) := h

private theorem ledger_unit_z :
    factorRegularLedger unitZFlag = 225346232239768793104584 := by
  norm_num [factorRegularLedger, factorPrimary, factorZTail, factorAllTail,
    flagMixed, unitZFlag, unitYZFlag, unitAllFlag,
    ContactNearPencil6600FlagResearch.agreementDirection6600,
    ContactNearPencil6600ArithmeticResearch.degreeIncidence,
    ContactNearPencil6600ArithmeticResearch.unitIncidence,
    ContactNearPencil6600ArithmeticResearch.errors,
    ContactNearPencil6600ArithmeticResearch.gap,
    ContactNearPencil6600ArithmeticResearch.agreements,
    ContactNearPencil6600ArithmeticResearch.n,
    ContactNearPencil6600ArithmeticResearch.w]

private theorem ledger_unit_yz :
    factorRegularLedger unitYZFlag = 3042638165126976246229224 := by
  norm_num [factorRegularLedger, factorPrimary, factorZTail, factorAllTail,
    flagMixed, unitZFlag, unitYZFlag, unitAllFlag,
    ContactNearPencil6600FlagResearch.agreementDirection6600,
    ContactNearPencil6600ArithmeticResearch.degreeIncidence,
    ContactNearPencil6600ArithmeticResearch.unitIncidence,
    ContactNearPencil6600ArithmeticResearch.errors,
    ContactNearPencil6600ArithmeticResearch.gap,
    ContactNearPencil6600ArithmeticResearch.agreements,
    ContactNearPencil6600ArithmeticResearch.n,
    ContactNearPencil6600ArithmeticResearch.w]

private theorem ledger_unit_all :
    factorRegularLedger unitAllFlag = 16475783575165773555434577 := by
  norm_num [factorRegularLedger, factorPrimary, factorZTail, factorAllTail,
    flagMixed, unitZFlag, unitYZFlag, unitAllFlag,
    ContactNearPencil6600FlagResearch.agreementDirection6600,
    ContactNearPencil6600ArithmeticResearch.degreeIncidence,
    ContactNearPencil6600ArithmeticResearch.unitIncidence,
    ContactNearPencil6600ArithmeticResearch.errors,
    ContactNearPencil6600ArithmeticResearch.gap,
    ContactNearPencil6600ArithmeticResearch.agreements,
    ContactNearPencil6600ArithmeticResearch.n,
    ContactNearPencil6600ArithmeticResearch.w]

/-- Linearized regular ledger in the three nested Newton support values. -/
def weightedLedger (total ys s : ℕ) : ℕ :=
  total * factorRegularLedger unitZFlag +
    ys * (factorRegularLedger unitYZFlag - factorRegularLedger unitZFlag) +
    s * (factorRegularLedger unitAllFlag - factorRegularLedger unitYZFlag)

theorem factorRegularLedger_weightedFlag (F : Poly3 K) :
    factorRegularLedger (weightedFlag F) =
      weightedLedger (swt flagTotalWeights F) (swt flagYSWeights F)
        (swt flagSWeights F) := by
  have hra := swt_s_le_ys F
  have hat := swt_ys_le_total F
  unfold swt at hra hat ⊢
  rw [factorRegularLedger_projection_decomposition]
  simp only [weightedFlag, weightedLedger, swt]
  rw [ledger_unit_z, ledger_unit_yz, ledger_unit_all]
  norm_num
  omega

/-- Every actual geometric factor has weighted-flag coordinates bounded by
its original source factor's three residual support functions. -/
theorem weightedFlag_bounds_of_surfaceFactor
    (phi : Polynomial K →+* L) (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (g : MvPolynomial (Fin 3) L) (hg : g ∈ surfaceFactors phi F) :
    (weightedFlag g).zOnly ≤
        MvPolynomial.weightedTotalDegree residualTotalWeights F ∧
      (weightedFlag g).yz ≤
        MvPolynomial.weightedTotalDegree residualYSWeights F ∧
      (weightedFlag g).all ≤
        MvPolynomial.weightedTotalDegree residualSWeights F := by
  have htotalSingle : swt flagTotalWeights g ≤
      ∑ h ∈ surfaceFactors phi F, swt flagTotalWeights h :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hg
  have hysSingle : swt flagYSWeights g ≤
      ∑ h ∈ surfaceFactors phi F, swt flagYSWeights h :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hg
  have hsSingle : swt flagSWeights g ≤
      ∑ h ∈ surfaceFactors phi F, swt flagSWeights h :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hg
  have htotal := htotalSingle.trans
    ((surfaceFactors_swt_budget flagTotalWeights phi hphi F hF).trans
      (surfaceMap_swt_total_le phi F))
  have hys := hysSingle.trans
    ((surfaceFactors_swt_budget flagYSWeights phi hphi F hF).trans
      (surfaceMap_swt_ys_le phi F))
  have hs := hsSingle.trans
    ((surfaceFactors_swt_budget flagSWeights phi hphi F hF).trans
      (surfaceMap_swt_s_le phi F))
  simp only [weightedFlag]
  exact ⟨(Nat.sub_le _ _).trans htotal,
    (Nat.sub_le _ _).trans hys, hs⟩

/-- The cumulative coordinates of a factor's canonical flag are bounded by
its source polynomial's three nested support functions. -/
theorem weightedFlag_cumulative_bounds_of_surfaceFactor
    (phi : Polynomial K →+* L) (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (g : MvPolynomial (Fin 3) L) (hg : g ∈ surfaceFactors phi F) :
    (weightedFlag g).zOnly + (weightedFlag g).yz + (weightedFlag g).all ≤
        MvPolynomial.weightedTotalDegree residualTotalWeights F ∧
      (weightedFlag g).yz + (weightedFlag g).all ≤
        MvPolynomial.weightedTotalDegree residualYSWeights F ∧
      (weightedFlag g).all ≤
        MvPolynomial.weightedTotalDegree residualSWeights F := by
  have htotalSingle : swt flagTotalWeights g ≤
      ∑ h ∈ surfaceFactors phi F, swt flagTotalWeights h :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hg
  have hysSingle : swt flagYSWeights g ≤
      ∑ h ∈ surfaceFactors phi F, swt flagYSWeights h :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hg
  have hsSingle : swt flagSWeights g ≤
      ∑ h ∈ surfaceFactors phi F, swt flagSWeights h :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hg
  have htotal := htotalSingle.trans
    ((surfaceFactors_swt_budget flagTotalWeights phi hphi F hF).trans
      (surfaceMap_swt_total_le phi F))
  have hys := hysSingle.trans
    ((surfaceFactors_swt_budget flagYSWeights phi hphi F hF).trans
      (surfaceMap_swt_ys_le phi F))
  have hs := hsSingle.trans
    ((surfaceFactors_swt_budget flagSWeights phi hphi F hF).trans
      (surfaceMap_swt_s_le phi F))
  have hra := swt_s_le_ys g
  have hat := swt_ys_le_total g
  simp only [weightedFlag]
  constructor
  · omega
  constructor
  · omega
  · exact hs

/-- A geometric factor family is charged only by the three source Newton
support functions, not by independent coordinate maxima. -/
theorem sum_surfaceFactor_ledgers_le
    (phi : Polynomial K →+* L) (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g ∈ surfaceFactors phi F, factorRegularLedger (weightedFlag g)) ≤
      weightedLedger
        (MvPolynomial.weightedTotalDegree residualTotalWeights F)
        (MvPolynomial.weightedTotalDegree residualYSWeights F)
        (MvPolynomial.weightedTotalDegree residualSWeights F) := by
  classical
  rw [show (∑ g ∈ surfaceFactors phi F,
      factorRegularLedger (weightedFlag g)) =
      weightedLedger
        (∑ g ∈ surfaceFactors phi F, swt flagTotalWeights g)
        (∑ g ∈ surfaceFactors phi F, swt flagYSWeights g)
        (∑ g ∈ surfaceFactors phi F, swt flagSWeights g) by
    simp only [factorRegularLedger_weightedFlag, weightedLedger,
      Finset.sum_add_distrib, Finset.sum_mul]]
  unfold weightedLedger
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul_right _
        ((surfaceFactors_swt_budget flagTotalWeights phi hphi F hF).trans
          (surfaceMap_swt_total_le phi F))
    · exact Nat.mul_le_mul_right _
        ((surfaceFactors_swt_budget flagYSWeights phi hphi F hF).trans
          (surfaceMap_swt_ys_le phi F))
  · exact Nat.mul_le_mul_right _
      ((surfaceFactors_swt_budget flagSWeights phi hphi F hF).trans
        (surfaceMap_swt_s_le phi F))


theorem global_surface_weight_budgets
    (Q : MvPolynomial (Fin 4) K)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    MvPolynomial.weightedTotalDegree residualSWeights Q ≤ 8 ∧
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ 43 ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights Q ≤ 528 := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights Q 8).mpr
    intro d hd
    have hb := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    simp [residualSWeights]
    exact hb.2.1
  · constructor
    · apply (weightedTotalDegree_le_iff residualYSWeights Q 43).mpr
      intro d hd
      have hb := hbox hd
      rw [ContactFactorCaps.weight_fin4]
      simp [residualYSWeights]
      have hc := hb.2.2
      norm_num [weightedCap, ContactParameters6600Research.w,
        ContactParameters6600Research.multiplicity,
        ContactParameters6600Research.agreements,
        ContactParameters6600Research.n,
        ContactParameters6600Research.errors] at hc ⊢
      omega
    · apply (weightedTotalDegree_le_iff residualTotalWeights Q 528).mpr
      intro d hd
      have hb := hbox hd
      rw [ContactFactorCaps.weight_fin4]
      simp [residualTotalWeights]
      have hs := hb.1
      have hr := hb.2.1
      norm_num [seedTotalCap, slopeCap] at hs hr ⊢
      omega

/-- The actual positive-`R` factor family fits the sharp global weighted
ledger `(total,YS,R)=(528,43,8)`. -/
theorem positiveRFactors_weightedLedger_budget
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    (∑ F ∈ positiveRFactors Q,
      weightedLedger
        (MvPolynomial.weightedTotalDegree residualTotalWeights F)
        (MvPolynomial.weightedTotalDegree residualYSWeights F)
        (MvPolynomial.weightedTotalDegree residualSWeights F)) ≤
      weightedLedger 528 43 8 := by
  classical
  have hprod := positiveRFactors_product_dvd Q hQ
  have htotal := sum_weighted_degrees_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hprod
  have hys := sum_weighted_degrees_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hprod
  have hs := sum_weighted_degrees_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hprod
  have hboxw := global_surface_weight_budgets Q hbox
  have htotal' := Nat.mul_le_mul_right
    (factorRegularLedger unitZFlag) (htotal.trans hboxw.2.2)
  have hys' := Nat.mul_le_mul_right
    (factorRegularLedger unitYZFlag - factorRegularLedger unitZFlag)
    (hys.trans hboxw.2.1)
  have hs' := Nat.mul_le_mul_right
    (factorRegularLedger unitAllFlag - factorRegularLedger unitYZFlag)
    (hs.trans hboxw.1)
  calc
    (∑ F ∈ positiveRFactors Q,
      weightedLedger
        (MvPolynomial.weightedTotalDegree residualTotalWeights F)
        (MvPolynomial.weightedTotalDegree residualYSWeights F)
        (MvPolynomial.weightedTotalDegree residualSWeights F)) =
      (∑ F ∈ positiveRFactors Q,
        MvPolynomial.weightedTotalDegree residualTotalWeights F) *
          factorRegularLedger unitZFlag +
      (∑ F ∈ positiveRFactors Q,
        MvPolynomial.weightedTotalDegree residualYSWeights F) *
          (factorRegularLedger unitYZFlag - factorRegularLedger unitZFlag) +
      (∑ F ∈ positiveRFactors Q,
        MvPolynomial.weightedTotalDegree residualSWeights F) *
          (factorRegularLedger unitAllFlag - factorRegularLedger unitYZFlag) := by
        simp [weightedLedger, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ 528 * factorRegularLedger unitZFlag +
        43 * (factorRegularLedger unitYZFlag - factorRegularLedger unitZFlag) +
        8 * (factorRegularLedger unitAllFlag - factorRegularLedger unitYZFlag) :=
      Nat.add_le_add (Nat.add_le_add htotal' hys') hs'
    _ = weightedLedger 528 43 8 := rfl

def weightedRegularNumerator : ℕ := weightedLedger 528 43 8

def weightedTotalNumerator : ℕ :=
  weightedRegularNumerator +
    ContactParameters6600Research.retainedSingularContribution

def weightedLedgerCeiling : ℕ :=
  (weightedTotalNumerator + gap ^ 2 - 1) / gap ^ 2

theorem weighted_regular_exact :
    weightedRegularNumerator = 347591527017058221717222696 := by
  norm_num [weightedRegularNumerator, weightedLedger, ledger_unit_z,
    ledger_unit_yz, ledger_unit_all]

theorem weighted_total_exact :
    weightedTotalNumerator = 354634170199301256501330438 := by
  rw [show weightedTotalNumerator =
      weightedRegularNumerator +
        ContactParameters6600Research.retainedSingularContribution by rfl,
    weighted_regular_exact]
  norm_num [ContactParameters6600Research.retainedSingularContribution,
    ContactParameters6600Research.retainedSingularNumerator,
    ContactParameters6600Research.mixed,
    ContactParameters6600Research.liftedSurface,
    ContactParameters6600Research.implicitCut,
    ContactParameters6600Research.liftedLast,
    ContactParameters6600Research.liftedAgreement,
    ContactParameters6600Research.unitZ,
    ContactParameters6600Research.gap,
    ContactParameters6600Research.algebraicCap,
    ContactParameters6600Research.implicitWeightedCap,
    ContactParameters6600Research.implicitYCap,
    ContactParameters6600Research.errors,
    ContactParameters6600Research.n,
    ContactParameters6600Research.w,
    ContactParameters6600Research.agreements,
    ContactParameters6600Research.slopeCap,
    ContactParameters6600Research.seedTotalCap,
    ContactParameters6600Research.weightedCap,
    ContactParameters6600Research.multiplicity]

theorem weighted_ledger_ceiling_exact :
    weightedLedgerCeiling = 130759118598650684 := by
  norm_num [weightedLedgerCeiling, weighted_total_exact, gap, agreements, n,
    errors, w]

theorem weighted_strict_budget :
    weightedTotalNumerator < alignmentBudget * gap ^ 2 := by
  rw [weighted_total_exact]
  norm_num [alignmentBudget, gap, agreements, n, errors, w]

/-- The sharp weighted ledger is exactly the existing surface-flag ledger. -/
theorem weightedLedger_global_eq :
    weightedLedger 528 43 8 = factorRegularLedger surfaceFlag6600 := by
  rw [factorRegularLedger_projection_decomposition]
  norm_num [weightedLedger, ledger_unit_z, ledger_unit_yz, ledger_unit_all,
    surfaceFlag6600]

end

end ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research

#print axioms ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research.polynomialIn_weightedFlag
#print axioms ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research.sum_surfaceFactor_ledgers_le
#print axioms ProximityPrize.SubmissionLower.ContactWeightedRegularFactor6600Research.positiveRFactors_weightedLedger_budget

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCountParameterizedResearch
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount

/-!
# Asymmetric residual-stage decomposition

For a proper residual pair `(Q,T)`, only `Q` is split into its regular and
singular branches.  Thus no symmetric "both singular" case is needed:
regular positive-`R` factors of `Q` retain the equation `T = 0`, while the
whole singular branch is covered by the implicit-pair family and exceptional
set constructed from `Q` alone.

The final theorem below constructs that cover and both finite-family degree
budgets.  Its only count inputs are factorwise proper-cut inequalities and
implicit-pair inequalities.  These are deliberately factorwise rather than
one stage-wide geometric premise.
-/

namespace ProximityPrize.SubmissionLower.ContactAsymmetricResidualStageResearch

open scoped Classical BigOperators
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch ContactSingularLedger6600Research
open ContactSelectedSeedDecomposition ContactImplicitPairBudgets
open ContactImplicitContactLift ContactSingularAuxiliary ContactFactorCover
open ContactFactorCaps ContactInterpolation ContactTranslation
open ContactGenericSurface ContactGeometricFactorCover ContactGeometricFirstTail
open ContactGenericInitialPoint
open ContactOriginalRegularSeedCount ContactProperCutSeedCount ContactCountingCaps
open ContactPrimeSeedIncidence ActualCoordinateDegreeSum

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

abbrev RegularIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(positiveRFactors Q)

abbrev ImplicitIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(implicitPairSet (singularAuxiliary Q))

/-- The regular family keeps both equations of the residual pair. -/
def regularPairSeeds (Q T : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex Q) : Finset K :=
  Gamma.filter fun gamma ↦
    RegularSolution F.1 (selected gamma) gamma ∧
      specialization K (selected gamma) gamma T = 0

def implicitSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (q : ImplicitIndex Q) : Finset K :=
  Gamma.filter fun gamma ↦ LiftedSolutionPair q.1 (selected gamma) gamma

/-- The singular union depends only on the first equation `Q`. -/
def singularSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
    exceptionalSeeds (singularAuxiliary Q) Gamma selected

theorem regularPairSeeds_subset (Q T : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (F : RegularIndex Q) :
    regularPairSeeds Q T selected Gamma F ⊆ Gamma :=
  Finset.filter_subset _ _

theorem implicitSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (q : ImplicitIndex Q) :
    implicitSeeds Q selected Gamma q ⊆ Gamma :=
  Finset.filter_subset _ _

theorem regularPairSeeds_data (Q T : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (F : RegularIndex Q)
    (gamma : K) (hgamma : gamma ∈ regularPairSeeds Q T selected Gamma F) :
    RegularSolution F.1 (selected gamma) gamma ∧
      specialization K (selected gamma) gamma T = 0 :=
  (Finset.mem_filter.mp hgamma).2

theorem implicitSeeds_data (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (q : ImplicitIndex Q)
    (gamma : K) (hgamma : gamma ∈ implicitSeeds Q selected Gamma q) :
    LiftedSolutionPair q.1 (selected gamma) gamma :=
  (Finset.mem_filter.mp hgamma).2

theorem singularSeeds_card_le_sum
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    (singularSeeds Q selected Gamma).card ≤
      (∑ q : ImplicitIndex Q, (implicitSeeds Q selected Gamma q).card) +
        (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right Finset.card_biUnion_le _)

/-! ## Actual asymmetric cover -/

/-- Apply the constructed three-way decomposition to `Q` only.  The second
equation is inserted only in the regular filters. -/
theorem card_le_regular_sum_add_singular
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w)
    (hDw : w < (2 * s - 1) * D)
    (hj : 1 ≤ (2 * s - 1) * L) (hjSmall : (2 * s - 1) * L < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0) :
    Gamma.card ≤
      (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) +
        (singularSeeds Q selected Gamma).card := by
  classical
  have hdecomp := selected_seed_decomposition Q hQ D w L s p hs hsmall hw
    hDw hj hjSmall hbox Gamma selected hQsolution
  let regularUnion := Finset.univ.biUnion (regularPairSeeds Q T selected Gamma)
  have hsub : Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma := by
    intro gamma hgamma
    by_cases hexc : gamma ∈ exceptionalSeeds (singularAuxiliary Q) Gamma selected
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hexc)
    · obtain ⟨F, hF, hreg⟩ | ⟨q, hq, himp⟩ := hdecomp.2.1 gamma hgamma hexc
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨⟨F, hF⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hgamma, hreg, hTsolution gamma hgamma⟩⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hgamma, himp⟩⟩
  calc
    Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card :=
      Finset.card_le_card hsub
    _ ≤ regularUnion.card + (singularSeeds Q selected Gamma).card :=
      Finset.card_union_le _ _
    _ ≤ (∑ F : RegularIndex Q,
          (regularPairSeeds Q T selected Gamma F).card) +
        (singularSeeds Q selected Gamma).card :=
      Nat.add_le_add_right Finset.card_biUnion_le _

/-! ## Properness of every regular carrier -/

/-- Recursive-GCD relative primality rules out divisibility of a positive-R
factor of `Q` into the second residual equation. -/
theorem regularFactor_not_dvd_second
    (Q T : MvPolynomial (Fin 4) K) (hrel : IsRelPrime Q T)
    (F : RegularIndex Q) : ¬ F.1 ∣ T := by
  obtain ⟨hirr, hdiv, _⟩ := positiveRFactors_spec Q F.1 F.2
  intro hFT
  exact hirr.not_isUnit (hrel hdiv hFT)

/-- Properness survives passage to every geometric factor over `K(X)^alg`.
This is the exact proper-cut premise required by `proper_cut_seed_bound`. -/
theorem geometricFactor_not_dvd_second
    (Q T : MvPolynomial (Fin 4) K) (hrel : IsRelPrime Q T)
    (F : RegularIndex Q)
    (g : MvPolynomial (Fin 3) (GenericField K))
    (hg : g ∈ surfaceFactors (polynomialEmbedding K) F.1) :
    ¬ g ∣ surfaceMap (polynomialEmbedding K) T := by
  obtain ⟨hFirr, _hFdiv, hFRpos⟩ := positiveRFactors_spec Q F.1 F.2
  obtain ⟨hgirred, hgdiv⟩ :=
    surfaceFactors_spec (polynomialEmbedding K) F.1 g hg
  have hpos : 0 < F.1.degreeOf 1 + F.1.degreeOf 2 + F.1.degreeOf 3 := by
    omega
  have hgeo : g ∣ geometricSurfaceMap K (GenericField K) F.1 := by
    simpa only [canonical_geometricSurfaceMap] using hgdiv
  intro hgT
  apply regularFactor_not_dvd_second Q T hrel F
  apply (geometric_factor_dvd_iff K (GenericField K) F.1 T hFirr hpos
    g hgirred hgeo).mp
  simpa only [canonical_geometricSurfaceMap] using hgT

/-! ## Linear factor and implicit-pair aggregation -/

def regularVector (P : UnequalParameters)
    (F : MvPolynomial (Fin 4) K) : ContactParameters6600Research.DegreeVector :=
  ⟨F.degreeOf 2 * P.rightZ + F.degreeOf 3 * P.rightR,
    F.degreeOf 1 * P.rightZ + F.degreeOf 3 * P.rightY,
    F.degreeOf 1 * P.rightR + F.degreeOf 2 * P.rightY⟩

def regularCapAt (v : ContactParameters6600Research.DegreeVector) : Fin 3 → ℕ :=
  ![v.y, v.r, v.z]

/-- Summed geometric mixed degrees are controlled by the original factor
degrees and the box of the unequal second equation. -/
theorem sum_coordinateMixedDegree_geometricFactors_le
    (P : UnequalParameters) (F T : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hTY : T.degreeOf 1 ≤ P.rightY) (hTR : T.degreeOf 2 ≤ P.rightR)
    (hTZ : T.degreeOf 3 ≤ P.rightZ) (i : Fin 3) :
    (∑ g : GeometricFactor K F,
      coordinateMixedDegree (GenericField K) g.1
        (surfaceMap (polynomialEmbedding K) T) i) ≤
      regularCapAt (regularVector P F) i := by
  classical
  have hsum (j : Fin 3) :
      (∑ g : GeometricFactor K F, g.1.degreeOf j) ≤ F.degreeOf j.succ :=
    geometricFactor_sum_degree_le K F hF j
  have hsum0 : (∑ g : GeometricFactor K F, g.1.degreeOf 0) ≤ F.degreeOf 1 := by
    simpa using hsum 0
  have hsum1 : (∑ g : GeometricFactor K F, g.1.degreeOf 1) ≤ F.degreeOf 2 := by
    simpa using hsum 1
  have hsum2 : (∑ g : GeometricFactor K F, g.1.degreeOf 2) ≤ F.degreeOf 3 := by
    have h := hsum 2
    rw [show (2 : Fin 3).succ = (3 : Fin 4) by decide] at h
    exact h
  have hT0 : (surfaceMap (polynomialEmbedding K) T).degreeOf 0 ≤ P.rightY :=
    (surfaceMap_degreeOf_le (polynomialEmbedding K) T 0).trans hTY
  have hT1 : (surfaceMap (polynomialEmbedding K) T).degreeOf 1 ≤ P.rightR :=
    (surfaceMap_degreeOf_le (polynomialEmbedding K) T 1).trans hTR
  have hT2 : (surfaceMap (polynomialEmbedding K) T).degreeOf 2 ≤ P.rightZ :=
    (surfaceMap_degreeOf_le (polynomialEmbedding K) T 2).trans hTZ
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · change (∑ geom : GeometricFactor K F,
        ((surfaceMap (polynomialEmbedding K) T).degreeOf 1 * geom.1.degreeOf 2 +
          geom.1.degreeOf 1 * (surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
        F.degreeOf 2 * P.rightZ + F.degreeOf 3 * P.rightR
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    simpa only [Nat.add_comm, Nat.mul_comm] using
      Nat.add_le_add (Nat.mul_le_mul hT1 hsum2)
        (Nat.mul_le_mul hsum1 hT2)
  · change (∑ geom : GeometricFactor K F,
        ((surfaceMap (polynomialEmbedding K) T).degreeOf 0 * geom.1.degreeOf 2 +
          geom.1.degreeOf 0 * (surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
        F.degreeOf 1 * P.rightZ + F.degreeOf 3 * P.rightY
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    simpa only [Nat.add_comm, Nat.mul_comm] using
      Nat.add_le_add (Nat.mul_le_mul hT0 hsum2)
        (Nat.mul_le_mul hsum0 hT2)
  · simp only [ActualCoordinateDegreeSum.coordinateMixedDegree_two,
      regularCapAt, regularVector, Matrix.cons_val_two]
    change (∑ geom : GeometricFactor K F,
        ((surfaceMap (polynomialEmbedding K) T).degreeOf 0 * geom.1.degreeOf 1 +
          geom.1.degreeOf 0 * (surfaceMap (polynomialEmbedding K) T).degreeOf 1)) ≤
        F.degreeOf 1 * P.rightR + F.degreeOf 2 * P.rightY
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    simpa only [Nat.add_comm, Nat.mul_comm] using
      Nat.add_le_add (Nat.mul_le_mul hT0 hsum1)
        (Nat.mul_le_mul hsum0 hT1)

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- The missing unequal-profile regular provider.  It refines one original
positive-`R` factor into the canonical geometric factors and obtains every
factorwise count directly from `proper_cut_seed_bound`. -/
theorem regularPairSeeds_bound
    (P : UnequalParameters) (Q T : MvPolynomial (Fin 4) K)
    (hrel : IsRelPrime Q T) (F : RegularIndex Q)
    (p : ℕ) [CharP K p]
    (hFY : F.1.degreeOf 1 ≤ P.leftY)
    (hFR : F.1.degreeOf 2 ≤ P.leftR)
    (hFZ : F.1.degreeOf 3 ≤ P.leftZ)
    (hTY : T.degreeOf 1 ≤ P.rightY)
    (hTR : T.degreeOf 2 ≤ P.rightR)
    (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p)
    (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p)
    (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n)
    (hw : 1 ≤ P.w) (hchar : P.w < p) (hwa : P.w < P.a)
    (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u₀ i + gamma * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
      (P.n - P.w) * dot P.agreement (regularVector P F.1) +
        (P.errors + 1) * P.gap * (regularVector P F.1).z := by
  classical
  let phi := polynomialEmbedding K
  let Delta := regularPairSeeds Q T selected Gamma F
  let carrierCap : ContactAlignmentParameters.DegreeVector :=
    ⟨P.leftY, P.leftR, P.leftZ⟩
  let cutCap : ContactAlignmentParameters.DegreeVector :=
    ⟨P.rightY, P.rightR, P.rightZ⟩
  have hFspec := positiveRFactors_spec Q F.1 F.2
  have hFne : F.1 ≠ 0 := hFspec.1.ne_zero
  have hDeltaSub : Delta ⊆ Gamma := regularPairSeeds_subset Q T selected Gamma F
  have hDeltaData (gamma : K) (hgamma : gamma ∈ Delta) :
      RegularSolution F.1 (selected gamma) gamma ∧
        specialization K (selected gamma) gamma T = 0 :=
    regularPairSeeds_data Q T selected Gamma F gamma hgamma
  have hcover := card_le_sum_geometricSeeds K F.1 hFne selected Delta
    (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
  letI : CharP (GenericField K) p := genericField_charP K p
  have hsingle (g : GeometricFactor K F.1) :
      (geometricSeeds K F.1 selected Delta g).card * P.gap ≤
        (P.n - P.w) * (∑ i : Fin 3,
          regularCapAt P.agreement i *
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap phi T) i) +
          (P.errors + 1) * P.gap *
            coordinateMixedDegree (GenericField K) g.1
              (surfaceMap phi T) 2 := by
    have hgSpec := surfaceFactors_spec phi F.1 g.1 g.2
    have hsub := geometricSeeds_subset K F.1 selected Delta g
    have hgCaps : HasCaps g.1 carrierCap := by
      intro i
      have hi := geometricFactor_degree_le K F.1 hFne g i
      fin_cases i
      · exact hi.trans hFY
      · exact hi.trans hFR
      · exact hi.trans hFZ
    have hTCaps : HasCaps (surfaceMap phi T) cutCap := by
      intro i
      fin_cases i
      · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
      · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
      · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
    have hcarrierSmall : ∀ i, capAt carrierCap i < p := by
      intro i
      fin_cases i
      · exact hleftYSmall
      · exact hleftRSmall
      · exact hleftZSmall
    have hgates := actual_characteristic_gates g.1 (surfaceMap phi T)
      carrierCap cutCap p hgCaps hTCaps hcarrierSmall
      (by simpa [carrierCap, cutCap, ContactAlignmentParameters.mixed,
          ContactAlignmentParameters.unitY, UnequalParameters.mixedCost,
          capAt, Nat.add_comm, Nat.mul_comm] using hmixedYSmall)
      (by simpa [carrierCap, cutCap, ContactAlignmentParameters.mixed,
          ContactAlignmentParameters.unitR, UnequalParameters.mixedCost,
          capAt, Nat.add_comm, Nat.mul_comm] using hmixedRSmall)
      (by simpa [carrierCap, cutCap, ContactAlignmentParameters.mixed,
          ContactAlignmentParameters.unitZ, UnequalParameters.mixedCost,
          capAt, Nat.add_comm, Nat.mul_comm] using hmixedZSmall)
    have hregular : ∀ gamma ∈ geometricSeeds K F.1 selected Delta g,
        MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
          (ContactPolynomialSolutions.polynomialPoint (phi.comp Polynomial.C)
            (selected gamma) gamma (phi Polynomial.X))
          (MvPolynomial.pderiv (2 : Fin 4) F.1) ≠ 0 := by
      intro gamma hgamma
      exact selectedPoint_regular_of_specialization K F.1 selected gamma
        (hDeltaData gamma (hsub hgamma)).1.2
    have hTpoint : ∀ gamma ∈ geometricSeeds K F.1 selected Delta g,
        MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T) = 0 := by
      intro gamma hgamma
      rw [selectedPoint_surface_evaluation,
        (hDeltaData gamma (hsub hgamma)).2, map_zero]
    have hcap (node : ι) : ∀ j,
        (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
          regularCapAt P.agreement j := by
      have h := surface_agreement_caps phi F.1 P.leftY P.leftR P.leftZ hleftR
        hFY hFR hFZ P.w (fun j => (j.factorial : K)⁻¹)
        (x node) (u₀ node) (u₁ node)
      intro j
      have hj :
          (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
            capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j := by
        simpa [agreementPolynomial] using h j
      fin_cases j
      · apply hj.trans
        change P.leftAgreement.y ≤ max P.leftAgreement.y P.rightAgreement.y
        exact le_max_left _ _
      · apply hj.trans
        change P.leftAgreement.r ≤ max P.leftAgreement.r P.rightAgreement.r
        exact le_max_left _ _
      · apply hj.trans
        change P.leftAgreement.z ≤ max P.leftAgreement.z P.rightAgreement.z
        exact le_max_left _ _
    have hcount := proper_cut_seed_bound phi F.1 g.1 (surfaceMap phi T)
      hgSpec.1 hgSpec.2 (geometricFactor_not_dvd_second Q T hrel F g.1 g.2)
      selected (geometricSeeds K F.1 selected Delta g) nodes x u₀ u₁ hinj
      p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
      hgates.1 hgates.2
      (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
      (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
      hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
      hTpoint
      (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
      (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
        (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
      (regularCapAt P.agreement) (fun node _ => hcap node)
    simpa [hnodes, UnequalParameters.gap] using hcount
  have hbudget (i : Fin 3) :=
    sum_coordinateMixedDegree_geometricFactors_le P F.1 T hFne hTY hTR hTZ i
  have hfubini :
      (∑ g : GeometricFactor K F.1, ∑ i : Fin 3,
          regularCapAt P.agreement i *
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i) =
        ∑ i : Fin 3, regularCapAt P.agreement i *
          (∑ g : GeometricFactor K F.1,
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Delta.card * P.gap ≤
        (∑ g : GeometricFactor K F.1,
          (geometricSeeds K F.1 selected Delta g).card) * P.gap :=
      Nat.mul_le_mul_right P.gap hcover
    _ = ∑ g : GeometricFactor K F.1,
        (geometricSeeds K F.1 selected Delta g).card * P.gap := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F.1,
        ((P.n - P.w) * (∑ i : Fin 3, regularCapAt P.agreement i *
          coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i) +
          (P.errors + 1) * P.gap *
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2) :=
      Finset.sum_le_sum (fun g _ => hsingle g)
    _ = (P.n - P.w) * (∑ i : Fin 3, regularCapAt P.agreement i *
          (∑ g : GeometricFactor K F.1,
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)) +
        (P.errors + 1) * P.gap *
          (∑ g : GeometricFactor K F.1,
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfubini]
    _ ≤ (P.n - P.w) * (∑ i : Fin 3,
          regularCapAt P.agreement i * regularCapAt (regularVector P F.1) i) +
        (P.errors + 1) * P.gap * regularCapAt (regularVector P F.1) 2 :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ (Finset.sum_le_sum
          (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
        (Nat.mul_le_mul_left _ (hbudget 2))
    _ = (P.n - P.w) * dot P.agreement (regularVector P F.1) +
        (P.errors + 1) * P.gap * (regularVector P F.1).z := by
      simp [Fin.sum_univ_three, regularCapAt, dot]

/-- Box-level wrapper producing exactly the `hregular` family consumed by
`asymmetric_stage_count_lt`. -/
theorem all_regularPairSeeds_bound
    (P : UnequalParameters) (Q T : MvPolynomial (Fin 4) K)
    (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (D w L s p : ℕ) [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hwBox : 1 ≤ w)
    (hY : (D - 1) / w ≤ P.leftY)
    (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ)
    (hTY : T.degreeOf 1 ≤ P.rightY)
    (hTR : T.degreeOf 2 ≤ P.rightR)
    (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p)
    (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p)
    (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n)
    (hw : 1 ≤ P.w) (hchar : P.w < p) (hwa : P.w < P.a)
    (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u₀ i + gamma * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    ∀ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
        (P.n - P.w) * dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z := by
  intro F
  have hFbox := (directFactor_data Q F.1 hQ D w L s hbox F.2).2.2
  have hFcaps := degree_bounds_of_mem_box F.1 D w L s hwBox hFbox
  exact regularPairSeeds_bound P Q T hrel F p
    (hFcaps.1.trans (by simpa using hY))
    (hFcaps.2.1.trans hR) (hFcaps.2.2.trans hZ)
    hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u₀ u₁
    hinj hnodes hw hchar hwa han hdegree hagreement hnoPencil

def implicitVector (q : (_ : MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K) :
    ContactParameters6600Research.DegreeVector :=
  ⟨pairYCost (K := K) q, pairRCost (K := K) q, pairZCost (K := K) q⟩

theorem regularVector_budgets
    (P : UnequalParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s : ℕ) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hY : (D - 1) / w ≤ P.leftY)
    (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ) :
    (∑ F : RegularIndex Q, (regularVector P F.1).y) ≤ P.mixedCost.y ∧
      (∑ F : RegularIndex Q, (regularVector P F.1).r) ≤ P.mixedCost.r ∧
      (∑ F : RegularIndex Q, (regularVector P F.1).z) ≤ P.mixedCost.z := by
  classical
  have hb := directFactor_input_budgets Q hQ D w L s hw hbox
  have hbY : (∑ F : RegularIndex Q, F.1.degreeOf (1 : Fin 4)) ≤ (D - 1) / w := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ ↦ Iff.rfl)]
    exact hb.1
  have hbR : (∑ F : RegularIndex Q, F.1.degreeOf (2 : Fin 4)) ≤ s := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ ↦ Iff.rfl)]
    exact hb.2.1
  have hbZ : (∑ F : RegularIndex Q, F.1.degreeOf (3 : Fin 4)) ≤ L := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ ↦ Iff.rfl)]
    exact hb.2.2
  simp only [regularVector, Finset.sum_add_distrib]
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right P.rightZ (hbR.trans hR))
      (Nat.mul_le_mul_right P.rightR (hbZ.trans hZ))
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right P.rightZ (hbY.trans hY))
      (Nat.mul_le_mul_right P.rightY (hbZ.trans hZ))
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right P.rightR (hbY.trans hY))
      (Nat.mul_le_mul_right P.rightY (hbR.trans hR))

theorem dot_sum_right {I : Type} [Fintype I]
    (v : I → ContactParameters6600Research.DegreeVector)
    (a : ContactParameters6600Research.DegreeVector) :
    dot a (ContactSingularLedger6600Research.sumVector v) = ∑ i, dot a (v i) := by
  calc
    _ = dot (ContactSingularLedger6600Research.sumVector v) a := by
      simp only [dot]
      ring
    _ = ∑ i, dot (v i) a :=
      ContactSingularLedger6600Research.dot_sum_left v a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [dot]
      ring

theorem sum_regular_counts_bound
    (P : UnequalParameters) (Q T : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hcost :
      (∑ F : RegularIndex Q, (regularVector P F.1).y) ≤ P.mixedCost.y ∧
      (∑ F : RegularIndex Q, (regularVector P F.1).r) ≤ P.mixedCost.r ∧
      (∑ F : RegularIndex Q, (regularVector P F.1).z) ≤ P.mixedCost.z)
    (hcount : ∀ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
        (P.n - P.w) * dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z) :
    (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) *
        P.gap ≤ P.regularNumerator := by
  calc
    _ = ∑ F : RegularIndex Q,
        (regularPairSeeds Q T selected Gamma F).card * P.gap := by
      rw [Finset.sum_mul]
    _ ≤ ∑ F : RegularIndex Q,
        ((P.n - P.w) * dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z) :=
      Finset.sum_le_sum fun F _ ↦ hcount F
    _ = (P.n - P.w) * dot P.agreement
          (ContactSingularLedger6600Research.sumVector fun F : RegularIndex Q ↦
            regularVector P F.1) +
        (P.errors + 1) * P.gap *
          (ContactSingularLedger6600Research.sumVector fun F : RegularIndex Q ↦
            regularVector P F.1).z := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← dot_sum_right]
      simp only [ContactSingularLedger6600Research.sumVector]
    _ ≤ (P.n - P.w) * dot P.agreement P.mixedCost +
        (P.errors + 1) * P.gap * P.mixedCost.z := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_left P.agreement.y hcost.1)
            (Nat.mul_le_mul_left P.agreement.r hcost.2.1))
          (Nat.mul_le_mul_left P.agreement.z hcost.2.2))
      · exact Nat.mul_le_mul_left _ hcost.2.2
    _ = P.regularNumerator := rfl

/-- Complete asymmetric stage composition.  The cover, regular factor
budgets, implicit-pair budgets, and exceptional count are all constructed.
Only the two already-local count interfaces remain factorwise inputs. -/
theorem asymmetric_stage_count_lt
    (P : UnequalParameters) (S : TightParameters)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p]
    (hs : 1 ≤ S.s) (hsmall : S.s < p) (hw : 1 ≤ S.w)
    (hDw : S.w < (2 * S.s - 1) * S.D)
    (hj : 1 ≤ (2 * S.s - 1) * S.L)
    (hjSmall : (2 * S.s - 1) * S.L < p)
    (hbox : Q ∈ globalCoefficientBox K S.D S.w S.L S.s)
    (hgap : 0 < P.gap) (hgapEq : S.gap = P.gap)
    (hY : (S.D - 1) / S.w ≤ P.leftY)
    (hR : S.s ≤ P.leftR) (hZ : S.L ≤ P.leftZ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0)
    (hregular : ∀ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
        (P.n - P.w) * dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z)
    (himplicit : ∀ q : ImplicitIndex Q,
      (implicitSeeds Q selected Gamma q).card * S.gap ≤
        (S.n - S.w) * dot S.agreement (implicitVector q.1) +
          (S.errors + 1) * S.gap * (implicitVector q.1).z) :
    Gamma.card < P.regularCountCap + S.countCap + 1 := by
  classical
  have hcover := card_le_regular_sum_add_singular Q T hQ S.D S.w S.L S.s p
    hs hsmall hw hDw hj hjSmall hbox selected Gamma hQsolution hTsolution
  have hdecomp := selected_seed_decomposition Q hQ S.D S.w S.L S.s p
    hs hsmall hw hDw hj hjSmall hbox Gamma selected hQsolution
  have hregularScaled := sum_regular_counts_bound P Q T selected Gamma
    (regularVector_budgets P Q hQ S.D S.w S.L S.s (by omega) hbox hY hR hZ)
    hregular
  have hregularCap :
      (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) ≤
        P.regularCountCap :=
    P.regular_count_le _ hgap hregularScaled
  have himplicitBudgets :
      (∑ q : ImplicitIndex Q, (implicitVector q.1).y) ≤ S.algebraicCap ∧
      (∑ q : ImplicitIndex Q, (implicitVector q.1).r) ≤
        2 * S.implicitYCap * S.algebraicCap ∧
      (∑ q : ImplicitIndex Q, (implicitVector q.1).z) ≤ S.implicitYCap := by
    constructor
    · change (∑ q ∈ (implicitPairSet (singularAuxiliary Q)).attach,
          pairYCost (K := K) q.1) ≤ S.algebraicCap
      rw [Finset.sum_attach]
      simpa [implicitVector, TightParameters.algebraicCap,
        TightParameters.implicitYCap, TightParameters.kappa] using hdecomp.2.2.2.1
    constructor
    · change (∑ q ∈ (implicitPairSet (singularAuxiliary Q)).attach,
          pairRCost (K := K) q.1) ≤ 2 * S.implicitYCap * S.algebraicCap
      rw [Finset.sum_attach]
      simpa [implicitVector, TightParameters.algebraicCap,
        TightParameters.implicitYCap, TightParameters.kappa] using hdecomp.2.2.2.2.1
    · change (∑ q ∈ (implicitPairSet (singularAuxiliary Q)).attach,
          pairZCost (K := K) q.1) ≤ S.implicitYCap
      rw [Finset.sum_attach]
      simpa [implicitVector, TightParameters.algebraicCap,
        TightParameters.implicitYCap, TightParameters.kappa] using hdecomp.2.2.2.2.2
  have hexceptions :
      (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
        2 * S.algebraicCap ^ 2 := by
    simpa [TightParameters.algebraicCap, TightParameters.kappa] using hdecomp.1
  have hsingularScaled := S.with_exceptions_bound
    (fun q : ImplicitIndex Q ↦ (implicitSeeds Q selected Gamma q).card)
    (fun q : ImplicitIndex Q ↦ implicitVector q.1)
    (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
    himplicitBudgets.1 himplicitBudgets.2.1 himplicitBudgets.2.2
    himplicit hexceptions
  have hsingularUnionScaled :
      (singularSeeds Q selected Gamma).card * S.gap ≤ S.tightNumerator :=
    (Nat.mul_le_mul_right S.gap
      (singularSeeds_card_le_sum Q selected Gamma)).trans hsingularScaled
  have hSgap : 0 < S.gap := by simpa [hgapEq] using hgap
  have hsingularCap : (singularSeeds Q selected Gamma).card ≤ S.countCap :=
    S.count_le_countCap _ hSgap hsingularUnionScaled
  omega

end

end ProximityPrize.SubmissionLower.ContactAsymmetricResidualStageResearch

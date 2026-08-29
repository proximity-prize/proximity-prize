import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
import ProximityPrize.SubmissionLower.ContactSeedlessProperCutResearch
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
import ProximityPrize.SubmissionLower.ContactImplicitContactLift
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactExceptionalSeedCount
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition

/-!
# Fixed-centre scalar list bound at the 67.30 radius

The seedless interpolant is factored exactly as in the affine alignment
argument.  Positive-`R` factors are counted on the plane curve `Z=0` using
one agreement incidence.  The `R`-independent auxiliary is a genuine
univariate polynomial in `Y` over the generic coefficient field, so its
distinct polynomial roots are counted directly.
-/

namespace ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation ContactInterpolation ContactPolynomialSolutions
open ContactFactorCaps ContactImplicitContactLift ContactTaylorNumerators
open ContactGenericSurface ContactGenericInitialPoint ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactSingularAuxiliary
open ContactSingularDegreeBounds
open ContactSelectedSeedDecomposition
open ContactSeedlessInterpolationResearch
open ContactSeedlessPrimeIncidenceResearch ContactSeedlessProperCutResearch
open ActualCoordinateDegreeSum

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def prime : ℕ := 2130706433
def gap : ℕ := agreements - w
def capY : ℕ := 1 + 2 * w * yTotalCap
def capR : ℕ := w * (2 * slopeCap - 1)
def agreementCap : Fin 3 → ℕ := ![capY, capR, 1]
def regularListNumerator : ℕ :=
  (n - w) * (capY * slopeCap + capR * yTotalCap)
def singularListCap : ℕ := (2 * slopeCap - 1) * yTotalCap
def listNumerator : ℕ := regularListNumerator + singularListCap * gap
def listBudget : ℕ := 1300000000

theorem numeric_values :
    gap = 51007 ∧ capY = 17825657 ∧ capR = 3538917 ∧
      regularListNumerator = 64252712579442 ∧
      singularListCap = 1836 ∧ listNumerator = 64252806228294 := by
  norm_num [gap, capY, capR, regularListNumerator, singularListCap,
    listNumerator, agreements, n, errors, w, yTotalCap, slopeCap]

theorem list_numerator_fits : listNumerator < listBudget * gap := by
  norm_num [listNumerator, regularListNumerator, singularListCap, listBudget,
    gap, capY, capR, agreements, n, errors, w, yTotalCap, slopeCap]

/-- Exact strict integer ceiling before rounding the protocol reserve up. -/
theorem list_strict_ceiling_exact :
    listNumerator / gap + 1 = 1259686048 ∧
      listNumerator < 1259686048 * gap ∧
      1259686048 < listBudget := by
  norm_num [listNumerator, regularListNumerator, singularListCap, listBudget,
    gap, capY, capR, agreements, n, errors, w, yTotalCap, slopeCap]

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

theorem seedless_degree_caps
    (Q : MvPolynomial (Fin 4) K)
    (hbox : Q ∈ ContactSeedlessInterpolationResearch.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap) :
    Q.degreeOf 1 ≤ yTotalCap ∧ Q.degreeOf 2 ≤ slopeCap ∧
      Q.degreeOf 3 = 0 := by
  refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
    MvPolynomial.degreeOf_le_iff.mpr ?_, ?_⟩
  · intro d hd
    exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
  · intro d hd
    exact (hbox hd).2.1
  · apply Nat.eq_zero_of_le_zero
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.2.1.le

theorem agreement_cap
    (phi : Polynomial K →+* GenericField K)
    (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ yTotalCap)
    (hR : F.degreeOf 2 ≤ slopeCap)
    (hZ : F.degreeOf 3 = 0) (x u : K) :
    ∀ j, (agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j := by
  have hb := agreementNumerator_degree_bounds F yTotalCap slopeCap 0
    (by norm_num [slopeCap]) hY hR hZ.le w
      (fun j => (j.factorial : K)⁻¹) x u 0
  intro j
  fin_cases j
  · exact (surfaceMap_degreeOf_le phi _ 0).trans
      (hb.1.trans (by simp [agreementCap, capY]))
  · exact (surfaceMap_degreeOf_le phi _ 1).trans
      (hb.2.1.trans (by simp [agreementCap, capR]))
  · exact (surfaceMap_degreeOf_le phi _ 2).trans
      (hb.2.2.trans (by simp [agreementCap]))

abbrev GeometricFactor (F : MvPolynomial (Fin 4) K) :=
  ContactOriginalRegularSeedCount.GeometricFactor K F

def geometricPolynomials (F : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) (g : GeometricFactor K F) :
    Finset (Polynomial K) := by
  classical
  exact Gamma.filter (fun P ↦
    ContactOriginalRegularSeedCount.GeometricFactor.PolynomialFactor K F P 0 g)

theorem distinct_geometric_roots_bound
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hdeg : F.degreeOf 1 ≤ yTotalCap ∧ F.degreeOf 2 ≤ slopeCap ∧
      F.degreeOf 3 = 0)
    (Gamma : Finset (Polynomial K))
    (g : GeometricFactor K F)
    (hdegGamma : ∀ P ∈ Gamma, P.natDegree ≤ w)
    (received : IRSProfile.Index → K)
    (hvalues : ∀ P ∈ Gamma, agreements ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        P.eval (IRSProfile.domain i) = received i)).card) :
    (geometricPolynomials K F Gamma g).card * gap ≤
      regularListNumerator := by
  classical
  have hreg := seedless_geometric_regular_bound K F hF hdeg.1 hdeg.2.1
    hdeg.2.2 Gamma g hdegGamma received hvalues
  have hnum : (n - w) * (capY * slopeCap + capR * yTotalCap) =
      regularListNumerator := rfl
  rw [← hnum]
  exact hreg

/-- Count of solutions with Z-degree zero is bounded by listBudget. -/
theorem distinct_solutions_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ ContactSeedlessInterpolationResearch.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap)
    (Gamma : Finset (Polynomial K))
    (hdeg : ∀ P ∈ Gamma, P.natDegree ≤ w)
    (received : IRSProfile.Index → K)
    (hvalues : ∀ P ∈ Gamma, agreements ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        P.eval (IRSProfile.domain i) = received i)).card)
    (hroot : ∀ P ∈ Gamma,
      ContactTranslation.specialization K P 0 Q = 0) :
    Gamma.card < listBudget := by
  classical
  have hdegQ := seedless_degree_caps K Q hbox
  have hcard := seedless_factor_decomposition_count K Q hQ
    hdegQ.1 hdegQ.2.1 hdegQ.2.2 Gamma hdeg received hvalues hroot
  have hnum : Gamma.card * gap ≤ listNumerator := by
    calc
      Gamma.card * gap ≤
          (n - w) * (capY * slopeCap + capR * yTotalCap) +
            (2 * slopeCap - 1) * yTotalCap * gap := hcard
      _ = listNumerator := by
        unfold listNumerator regularListNumerator singularListCap
        rfl
  have hfits := list_numerator_fits
  have hpos : 0 < gap := by norm_num [gap, agreements, n, errors, w]
  exact Nat.lt_of_mul_lt_mul_right (hnum.trans_lt hfits)

theorem distinct_candidate_polynomials_bound
    (received : IRSProfile.Index → IRSProfile.Field)
    (Gamma : Finset (Polynomial IRSProfile.Field))
    (hdeg : ∀ P ∈ Gamma, P.natDegree ≤ w)
    (hvalues : ∀ P ∈ Gamma, agreements ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        P.eval (IRSProfile.domain i) = received i)).card) :
    Gamma.card < listBudget := by
  obtain ⟨Q, hQne, hbox, hvanish⟩ :=
    exists_frozen_seedless_vanishing_interpolant received
  have hroots : ∀ P ∈ Gamma,
      ContactTranslation.specialization IRSProfile.Field P 0 Q = 0 := by
    intro P hP
    exact hvanish P (Finset.univ.filter (fun i ↦
      P.eval (IRSProfile.domain i) = received i))
      (hdeg P hP) (hvalues P hP)
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
  exact distinct_solutions_bound IRSProfile.Field Q hQne hbox Gamma hdeg
    received hvalues hroots

end

end ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactOldCoreTerminalDerivative6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research
import ProximityPrize.SubmissionLower.ContactRFreeFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactSelectedCountHighTRepair6750Research
import ProximityPrize.SubmissionLower.ContactSmallProfileBFixedEquation6750Research
import ProximityPrize.SubmissionLower.ContactResidualValidity6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactOldCoreHighTEquationProvider6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactNestedFiveCapCoefficientBox6750Research
open ContactStackedSeedPartition6670Research
open ContactFlagBezout6543Research ContactPrimeSeedIncidence
open ContactIdentityCurveProvider6731Research
open ContactMovingOuterBudget6719Research
open ContactRobustFixedMeet6656Research
open ContactTightSingularLedgerResearch
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research
open ContactHighTDerivativeRouter6750Research
open ContactHighTDerivativeSelectorPositive6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactAnchoredOrdinaryProperProvider6750Research
open ContactAnchoredOrdinaryTangent6750Research
open ContactRFreeFixedSelectedCombinerResearch
open ContactResidualSupportParametersResearch
open ContactSelectedCount6750Research
open ContactHighTFixedSeedRepair6750Research
open ContactSelectedCountHighTRepair6750Research
open ContactSmallProfileBFixedEquation6750Research
open ContactOldCoreTerminalDerivative6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactResidualValidity6750Research
open ContactMovingAgreementCertificate6719Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

def terminalJ (t y r : Nat) : Nat := highTDerivativeOrder t y r
def terminalRR (t y r : Nat) : Nat := r - terminalJ t y r
def terminalYY (t y r : Nat) : Nat := y - terminalJ t y r
def terminalTT (t y r : Nat) : Nat := t - terminalJ t y r
def terminalRP (t y r : Nat) : Nat := max 2 (terminalRR t y r)
def terminalYP (t y r : Nat) : Nat :=
  max (terminalRP t y r + 1) (terminalYY t y r)
def terminalTP (t y r : Nat) : Nat :=
  max (terminalYP t y r) (terminalTT t y r)
def terminalTightR (t y r : Nat) : Nat := max 1 (terminalRR t y r)
def terminalD (t y r : Nat) : Nat := terminalDerivativeCutoff (terminalJ t y r)

 
def CellIdentityConditions (tp yp rp : Nat) : Prop :=
  (n - w) * (errors + 1) *
      identityCurveDegree unitZFlag (cellA tp yp) (cellB yp rp) (cellS rp) w ≤
    gap * flagMixed unitZFlag (cellFirstTail tp yp rp) (cellSecondTail tp yp rp) ∧
  (n - w) * (errors + 1) *
      identityCurveDegree unitYZFlag (cellA tp yp) (cellB yp rp) (cellS rp) w ≤
    gap * flagMixed unitYZFlag (cellFirstTail tp yp rp) (cellSecondTail tp yp rp) ∧
  (n - w) * (errors + 1) *
      identityCurveDegree unitAllFlag (cellA tp yp) (cellB yp rp) (cellS rp) w ≤
    gap * flagMixed unitAllFlag (cellFirstTail tp yp rp) (cellSecondTail tp yp rp)

def TerminalIdentityConditions (t y r : Nat) : Prop :=
  CellIdentityConditions (terminalTP t y r) (terminalYP t y r)
    (terminalRP t y r)

 
def TerminalGateConditions (t y r : Nat) : Prop :=
  let D := terminalD t y r
  let tt := terminalTT t y r
  let sr := terminalTightR t y r
  1 ≤ sr ∧ sr < prime ∧ 1 ≤ w ∧ w < prime ∧
  w < (2 * sr - 1) * D ∧
  1 ≤ (2 * sr - 1) * tt ∧
  (2 * sr - 1) * tt < prime ∧
  (cellTightProfile D tt sr).implicitYCap < prime ∧
  2 * (cellTightProfile D tt sr).implicitYCap *
      (cellTightProfile D tt sr).algebraicCap < prime ∧
  w < agreements ∧ agreements ≤ n

instance terminalIdentityConditionsDecidable (t y r : Nat) :
    Decidable (TerminalIdentityConditions t y r) := by
  unfold TerminalIdentityConditions CellIdentityConditions
  infer_instance

instance terminalGateConditionsDecidable (t y r : Nat) :
    Decidable (TerminalGateConditions t y r) := by
  unfold TerminalGateConditions
  infer_instance

 


theorem identityBasisBudget_of_basic_cell_analytic
    (t y r : Nat) (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t) :
    IdentityCellBasisBudget6750 t y r :=
  ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryFixedCell6750Research.identityBasisBudget_of_basic_cell_analytic
    t y r hr2 hry hyt

def TerminalGateConditionsAt (t r j : Nat) : Prop :=
  let D := terminalDerivativeCutoff j
  let tt := t - j
  let sr := max 1 (r - j)
  1 ≤ sr ∧ sr < prime ∧ 1 ≤ w ∧ w < prime ∧
  w < (2 * sr - 1) * D ∧
  1 ≤ (2 * sr - 1) * tt ∧
  (2 * sr - 1) * tt < prime ∧
  (cellTightProfile D tt sr).implicitYCap < prime ∧
  2 * (cellTightProfile D tt sr).implicitYCap *
      (cellTightProfile D tt sr).algebraicCap < prime ∧
  w < agreements ∧ agreements ≤ n

 


theorem combinerGatesD_of_terminal_bounds
    (D tt sr : Nat) (hDlo : w + 1 ≤ D) (hDhi : D ≤ profileA.weightedCap)
    (httLo : 1 ≤ tt) (httHi : tt ≤ 1698)
    (hsrLo : 1 ≤ sr) (hsrHi : sr ≤ 14) :
    OrdinaryCellCombinerGatesD6750 D tt sr :=
  ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryFixedCell6750Research.combinerGatesD_of_bounds_analytic
      D tt sr hDlo hDhi httLo (httHi.trans (by norm_num)) hsrLo
      (hsrHi.trans (by norm_num))

theorem terminal_conditions
    (t y r : Nat) (ht : t ≤ 1698) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hhigh : 1693 ≤ t) :
    TerminalIdentityConditions t y r ∧ TerminalGateConditions t y r := by
  have htt : t - 1693 < 6 := by omega
  have hrr : r - 2 < 13 := by omega
  have htEq : t - 1693 + 1693 = t := Nat.sub_add_cancel hhigh
  have hrEq : r - 2 + 2 = r := Nat.sub_add_cancel hr2
  have hjpos : 0 < terminalJ t y r := by
    exact highTDerivativeOrder_pos t y r
  let tf : Fin 1699 := ⟨t, Nat.lt_succ_iff.mpr ht⟩
  let yf : Fin 66 := ⟨y, Nat.lt_succ_iff.mpr hy⟩
  let rf : Fin 15 := ⟨r, Nat.lt_succ_iff.mpr hr⟩
  have hyt : y ≤ t := by omega
  have hcert := highTDerivativeOrder_certified tf yf rf hr2 hry
    (by simpa only [tf, yf] using hyt) hhigh
  have hjle : terminalJ t y r ≤ r := by
    simpa only [terminalJ, tf, yf, rf] using hcert.1.1
  have httLo : 1646 ≤ terminalTT t y r := by
    unfold terminalTT
    omega
  have hrpLo : 2 ≤ terminalRP t y r := Nat.le_max_left _ _
  have hrpHi : terminalRP t y r < 14 := by
    unfold terminalRP terminalRR
    omega
  have hypHi : terminalYP t y r < 65 := by
    unfold terminalYP terminalRP terminalRR terminalYY
    omega
  have hrpy : terminalRP t y r < terminalYP t y r := by
    unfold terminalYP
    omega
  have htp : terminalTP t y r = terminalTT t y r := by
    unfold terminalTP
    omega
  have hypTp : terminalYP t y r ≤ terminalTP t y r := by
    unfold terminalTP
    exact Nat.le_max_left _ _
  have hib := identityBasisBudget_of_basic_cell_analytic
    (terminalTP t y r) (terminalYP t y r) (terminalRP t y r)
    hrpLo hrpy hypTp
  have hDlo : w + 1 ≤ terminalD t y r := by
    unfold terminalD terminalDerivativeCutoff
    norm_num [profileA, ContactTwoTailParameters6750Research.Profile.weightedCap,
      w, agreements, n, errors]
    omega
  have hDhi : terminalD t y r ≤ profileA.weightedCap := by
    unfold terminalD terminalDerivativeCutoff
    exact Nat.sub_le _ _
  have httHi : terminalTT t y r ≤ 1698 := by
    unfold terminalTT
    exact (Nat.sub_le _ _).trans ht
  have hsrLo : 1 ≤ terminalTightR t y r := Nat.le_max_left _ _
  have hsrHi : terminalTightR t y r ≤ 14 := by
    unfold terminalTightR terminalRR
    omega
  have hg := combinerGatesD_of_terminal_bounds
    (terminalD t y r) (terminalTT t y r) (terminalTightR t y r)
    hDlo hDhi (by omega) httHi hsrLo hsrHi
  refine ⟨?_, ?_⟩
  · unfold TerminalIdentityConditions
    exact ⟨hib.zOnly, hib.yz, hib.all⟩
  · unfold TerminalGateConditions terminalD terminalTT terminalTightR
    exact ⟨hg.slope_pos, hg.slope_lt_char, hg.w_pos, hg.w_lt_char,
      hg.weighted_nontrivial, hg.algebraic_pos, hg.algebraic_lt_char,
      hg.implicitY_lt_char, hg.mixed_lt_char, hg.w_lt_agreements,
      hg.agreements_le_n⟩

theorem terminal_identityBudget
    (t y r : Nat) (ht : t ≤ 1698) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hhigh : 1693 ≤ t) :
    IdentityCellBudget6750 (terminalTP t y r) (terminalYP t y r)
      (terminalRP t y r) := by
  apply identityCellBudget_of_basis
  have h := (terminal_conditions t y r ht hy hr hr2 hry hhigh).1
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem terminal_combinerGates
    (t y r : Nat) (ht : t ≤ 1698) (hy : y ≤ 65) (hr : r ≤ 14)
    (hr2 : 2 ≤ r) (hry : r < y) (hhigh : 1693 ≤ t) :
    OrdinaryCellCombinerGatesD6750 (terminalD t y r)
      (terminalTT t y r) (terminalTightR t y r) := by
  have h := (terminal_conditions t y r ht hy hr hr2 hry hhigh).2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

 
theorem terminalDerivative_mem_padded_nestedFiveCap
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S) ∈
      nestedFiveCapCoefficientBox K (terminalDerivativeCutoff j) w
        (max (max (max 2 (oldCoreS S - j) + 1) (oldCoreYS S - j))
          (oldCoreTotal S - j))
        (max (max 2 (oldCoreS S - j) + 1) (oldCoreYS S - j))
        (max 2 (oldCoreS S - j)) := by
  intro d hd
  have hbox := terminalDerivative_mem_nestedFiveCap S j hj
  change ∀ e ∈ ((MvPolynomial.pderiv (2 : Fin 4))^[j]
      (oldCommonCore S)).support,
      e 1 + e 2 + e 3 ≤ oldCoreTotal S - j ∧
      e 1 + e 2 ≤ oldCoreYS S - j ∧
      e 2 ≤ oldCoreS S - j ∧
      e 0 + w * e 1 + (w - 1) * e 2 < terminalDerivativeCutoff j at hbox
  have h := hbox d hd
  exact ⟨h.1.trans (Nat.le_max_right _ _),
    h.2.1.trans (Nat.le_max_right _ _),
    h.2.2.1.trans (Nat.le_max_right _ _), h.2.2.2⟩

 
theorem residualSupportData_cell_of_nestedFiveCap
    (F : GlobalPoly) {D t y r : Nat}
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (hbox : F ∈ nestedFiveCapCoefficientBox K D w t y r) :
    ResidualSupportData (cellSupport t y r) F := by
  have hs : MvPolynomial.weightedTotalDegree residualSWeights F ≤ r := by
    apply (weightedTotalDegree_le_iff residualSWeights F r).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ t ∧ d 1 + d 2 ≤ y ∧
      d 2 ≤ r ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
    rw [ContactFactorCaps.weight_fin4]
    simpa [residualSWeights] using h.2.2.1
  have hys : MvPolynomial.weightedTotalDegree residualYSWeights F ≤ y := by
    apply (weightedTotalDegree_le_iff residualYSWeights F y).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ t ∧ d 1 + d 2 ≤ y ∧
      d 2 ≤ r ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
    rw [ContactFactorCaps.weight_fin4]
    simpa [residualYSWeights, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h.2.1
  have htotal : MvPolynomial.weightedTotalDegree residualTotalWeights F ≤ t := by
    apply (weightedTotalDegree_le_iff residualTotalWeights F t).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ t ∧ d 1 + d 2 ≤ y ∧
      d 2 ≤ r ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
    rw [ContactFactorCaps.weight_fin4]
    simpa [residualTotalWeights, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h.1
  refine ⟨?_, ?_, ?_⟩
  · change MvPolynomial.weightedTotalDegree residualSWeights F ≤ r - 2 + 2
    omega
  · change MvPolynomial.weightedTotalDegree residualYSWeights F ≤
      y - r - 1 + (r - 2) + 3
    omega
  · change MvPolynomial.weightedTotalDegree residualTotalWeights F ≤
      t - y + (y - r - 1) + (r - 2) + 3
    omega

 

theorem terminalDerivative_mem_padded_globalBox
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S) ∈
      ContactInterpolation.globalCoefficientBox K (terminalDerivativeCutoff j) w
        (max (max (max 2 (oldCoreS S - j) + 1) (oldCoreYS S - j))
          (oldCoreTotal S - j))
        (max 2 (oldCoreS S - j)) := by
  intro d hd
  have hbox := terminalDerivative_mem_padded_nestedFiveCap S j hj
  change ∀ e ∈ ((MvPolynomial.pderiv (2 : Fin 4))^[j]
      (oldCommonCore S)).support,
      e 1 + e 2 + e 3 ≤
          max (max (max 2 (oldCoreS S - j) + 1) (oldCoreYS S - j))
            (oldCoreTotal S - j) ∧
      e 1 + e 2 ≤ max (max 2 (oldCoreS S - j) + 1)
          (oldCoreYS S - j) ∧
      e 2 ≤ max 2 (oldCoreS S - j) ∧
      e 0 + w * e 1 + (w - 1) * e 2 < terminalDerivativeCutoff j at hbox
  have h := hbox d hd
  exact ⟨by omega, h.2.2.1, h.2.2.2⟩

 
theorem terminalDerivative_mem_tight_interpolationBox
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ oldCoreS S) :
    (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S) ∈
      ContactInterpolation.globalCoefficientBox K (terminalDerivativeCutoff j) w
        (oldCoreTotal S - j) (max 1 (oldCoreS S - j)) := by
  intro d hd
  have hbox := terminalDerivative_mem_nestedFiveCap S j hj
  change ∀ e ∈ ((MvPolynomial.pderiv (2 : Fin 4))^[j]
      (oldCommonCore S)).support,
      e 1 + e 2 + e 3 ≤ oldCoreTotal S - j ∧
      e 1 + e 2 ≤ oldCoreYS S - j ∧
      e 2 ≤ oldCoreS S - j ∧
      e 0 + w * e 1 + (w - 1) * e 2 < terminalDerivativeCutoff j at hbox
  have h := hbox d hd
  exact ⟨by omega, h.2.2.1.trans (Nat.le_max_right _ _), h.2.2.2⟩

 


theorem terminalDerivativeSeeds_card_le
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hhigh : 1693 ≤ oldCoreTotal S)
    (hr2 : 2 ≤ oldCoreS S) (hry : oldCoreS S < oldCoreYS S) :
    (terminalDerivativeSeeds (oldCommonCore S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC)
        (oldGHighDerivativeOrder S)).card ≤
      iteratedDerivativeReplacementCost (oldGHighDerivativeOrder S)
        (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) := by
  let t := oldCoreTotal S
  let y := oldCoreYS S
  let r := oldCoreS S
  let j := oldGHighDerivativeOrder S
  let Q := (MvPolynomial.pderiv (2 : Fin 4))^[j] (oldCommonCore S)
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  let E := terminalDerivativeSeeds (oldCommonCore S) selected Delta j
  have ht : t ≤ 1698 := by simpa only [t] using oldCommonCore_total_le S
  have hy : y ≤ 65 := by simpa only [y] using oldCommonCore_ys_le S
  have hr : r ≤ 14 := by simpa only [r] using oldCommonCore_slope_le S
  have hr2' : 2 ≤ r := by simpa only [r] using hr2
  have hry' : r < y := by simpa only [r, y] using hry
  have hhigh' : 1693 ≤ t := by simpa only [t] using hhigh
  have hyt : y ≤ t := by omega
  let tf : Fin 1699 := ⟨t, Nat.lt_succ_iff.mpr ht⟩
  let yf : Fin 66 := ⟨y, Nat.lt_succ_iff.mpr hy⟩
  let rf : Fin 15 := ⟨r, Nat.lt_succ_iff.mpr hr⟩
  have hcert := highTDerivativeOrder_certified tf yf rf hr2' hry'
    (by simpa only [tf, yf] using hyt) hhigh'
  have hj : j ≤ r := by
    simpa only [j, oldGHighDerivativeOrder, t, y, r, tf, yf, rf] using hcert.1.1
  have hjpos : 0 < j := by
    simpa only [j, oldGHighDerivativeOrder, t, y, r] using
      highTDerivativeOrder_pos t y r
  have hsub : E ⊆ Gamma := by
    intro gamma hgamma
    have hDelta : gamma ∈ Delta := (Finset.mem_filter.mp hgamma).1
    exact fixedSeeds_subset selected Gamma S.QA S.QB S.QC hDelta
  have hsolution : ∀ gamma ∈ E,
      specialization K (selected gamma) gamma Q = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hdegreeE : ∀ gamma ∈ E, (selected gamma).natDegree ≤ w :=
    fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
  have hagreementE : ∀ gamma ∈ E, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hsub hgamma)
  have hnoE : NoLargeSelectedPencil selected E w errors :=
    ContactProperCutSeedCount.noLargeSelectedPencil_mono
      selected Gamma E w errors hsub hnoPencil
  have hQ : Q ≠ 0 := by
    simpa only [Q, j, r] using terminalDerivative_ne_zero S j
      (by simpa only [r] using hj)
  have hboxTight : Q ∈ globalCoefficientBox K
      (terminalDerivativeCutoff j) w (t - j) (max 1 (r - j)) := by
    simpa only [Q, t, r] using terminalDerivative_mem_tight_interpolationBox S j
      (by simpa only [r] using hj)
  have hboxCell : Q ∈ globalCoefficientBox K
      (terminalDerivativeCutoff j) w
      (max (max (max 2 (r - j) + 1) (y - j)) (t - j))
      (max 2 (r - j)) := by
    simpa only [Q, t, y, r] using terminalDerivative_mem_padded_globalBox S j
      (by simpa only [r] using hj)
  have hnested : Q ∈ nestedFiveCapCoefficientBox K
      (terminalDerivativeCutoff j) w
      (max (max (max 2 (r - j) + 1) (y - j)) (t - j))
      (max (max 2 (r - j) + 1) (y - j)) (max 2 (r - j)) := by
    simpa only [Q, t, y, r] using terminalDerivative_mem_padded_nestedFiveCap S j
      (by simpa only [r] using hj)
  let rr := r - j
  let rp := max 2 rr
  let yy := y - j
  let yp := max (rp + 1) yy
  let tt := t - j
  let tp := max yp tt
  let sr := max 1 rr
  let D := terminalDerivativeCutoff j
  have hrp2 : 2 ≤ rp := Nat.le_max_left _ _
  have hrple : rp ≤ 14 := by
    simp only [rp, rr]
    omega
  have hryp : rp < yp := by
    simp only [yp]
    omega
  have hyple : yp ≤ 65 := by
    simp only [yp, rp, rr, yy]
    omega
  have hyptp : yp ≤ tp := by
    simp only [tp]
    exact Nat.le_max_left _ _
  have htple : tp ≤ 2530 := by
    simp only [tp, yp, rp, rr, yy, tt]
    omega
  have hsupport : ResidualSupportData (cellSupport tp yp rp) Q := by
    apply residualSupportData_cell_of_nestedFiveCap Q hrp2 hryp hyptp
    simpa only [tp, yp, rp, rr, yy, tt, D] using hnested
  have hDshort : w + 1 ≤ D := by
    simp only [D, terminalDerivativeCutoff]
    norm_num [profileA, ContactTwoTailParameters6750Research.Profile.weightedCap,
      w, agreements, n, errors]
    omega
  have hDchar : D < prime := by
    exact (Nat.sub_le _ _).trans_lt (by
      norm_num [D, terminalDerivativeCutoff, profileA,
        ContactTwoTailParameters6750Research.Profile.weightedCap,
        prime, agreements, n, errors])
  have hid : IdentityCellBudget6750 tp yp rp := by
    apply identityCellBudget_of_basis
    exact identityBasisBudget_of_basic_cell_analytic tp yp rp hrp2 hryp hyptp
  have hproper : ProperStageProviderD6750 D tp yp rp :=
    properStageProviderD6750_of_tangent D tp yp rp htple
      (hyple.trans (by norm_num)) (hrple.trans (by norm_num))
      hrp2 hryp hyptp (cellTangentProviderD6750 D tp yp rp hDshort hDchar)
  have hgates : OrdinaryCellCombinerGatesD6750 D tt sr := by
    have hDhi : D ≤ profileA.weightedCap := by
      simp only [D, terminalDerivativeCutoff]
      exact Nat.sub_le _ _
    have httLo : 1 ≤ tt := by simp only [tt]; omega
    have httHi : tt ≤ 1698 := by simp only [tt]; omega
    have hsrLo : 1 ≤ sr := by simp only [sr]; exact Nat.le_max_left _ _
    have hsrHi : sr ≤ 14 := by simp only [sr, rr]; omega
    exact combinerGatesD_of_terminal_bounds D tt sr hDshort hDhi
      httLo httHi hsrLo hsrHi
  by_cases hrr : 1 ≤ rr
  · have hcount := cell_count_le_mixedReplacementCostD
      D tp yp rp tt sr htple (hyple.trans (by norm_num))
      (hrple.trans (by norm_num)) hrp2 hryp hyptp
      hproper hid hDshort hDchar hgates Q hQ
      (by simpa only [D, tt, sr, rr] using hboxTight)
      (by simpa only [D, tp, rp, yp, rr, yy, tt] using hboxCell)
      hsupport selected E u0 u1 hsolution hdegreeE hagreementE hnoE
    simpa only [E, Delta, j, t, y, r, iteratedDerivativeReplacementCost,
      if_neg (Nat.ne_of_gt hjpos), rr, yy, tt, rp, yp, tp, sr, D,
      if_pos hrr, terminalDerivativeCutoff, Nat.max_comm] using hcount
  · have hrr0 : rr = 0 := by omega
    have hR : Q.degreeOf (2 : Fin 4) = 0 := by
      simpa only [Q, r, rr, hrr0] using
        terminalDerivative_degreeOf_R_eq S j (by simpa only [r] using hj)
    have hcount := global_count_le_tight_countCap_of_R_degree_zero
      (ordinaryProfileD D tt sr) (cellTightProfile D tt sr)
      (ordinaryAlignmentD D tt sr) (prime := prime)
      Q hQ (by simpa [ordinaryProfileD, D, tt, sr, rr] using hboxTight) hR
      hgates.slope_pos hgates.slope_lt_char hgates.w_pos hgates.w_lt_char
      hgates.weighted_nontrivial hgates.algebraic_pos hgates.algebraic_lt_char
      hgates.implicitY_lt_char hgates.mixed_lt_char hgates.w_lt_agreements
      hgates.agreements_le_n selected E (Finset.univ : Finset I)
      IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by change Fintype.card I = n; norm_num [I, n])
      hdegreeE hsolution hagreementE
      (by simpa [ordinaryProfileD,
        ContactRobustFixedMeet6656Research.Profile.errors,
        errors, agreements, n] using hnoE)
    simpa only [E, Delta, j, t, y, r, iteratedDerivativeReplacementCost,
      if_neg (Nat.ne_of_gt hjpos), rr, hrr0, yy, tt, rp, yp, tp, sr, D,
      if_neg (by omega : ¬ 1 ≤ 0), Nat.zero_add,
      terminalDerivativeCutoff, Nat.max_comm] using hcount

 

theorem highTOldGEquationProvider6750 : HighTOldGEquationProvider6750 := by
  intro u0 u1 S selected Gamma hdegree hagreement hnoPencil
    hhigh hr2 hry
  let tf : Fin 1699 := ⟨oldCoreTotal S,
    Nat.lt_succ_iff.mpr (oldCommonCore_total_le S)⟩
  let yf : Fin 66 := ⟨oldCoreYS S,
    Nat.lt_succ_iff.mpr (oldCommonCore_ys_le S)⟩
  let rf : Fin 15 := ⟨oldCoreS S,
    Nat.lt_succ_iff.mpr (oldCommonCore_slope_le S)⟩
  have hyt : oldCoreYS S ≤ oldCoreTotal S :=
    ContactSelectedCountHighTRepair6750Research.oldCommonCore_ys_le_total S
  have hroute := highTDerivativeOrder_certified tf yf rf hr2 hry hyt hhigh
  have hj14 : oldGHighDerivativeOrder S ≤ 14 := by
    have hjlt : oldGHighDerivativeOrder S < 15 := by
      simpa only [oldGHighDerivativeOrder, tf, yf, rf] using hroute.2
    omega
  let validity : ResidualCellValidity6750
      (oldCoreTotal S - 1) (oldCoreYS S - 1)
        (oldCoreS S - 1) (oldCoreS S) :=
    residualCellValidity_of_bounded_cell tf yf rf
  have hterminal := terminalDerivativeSeeds_card_le S selected Gamma
    hdegree hagreement hnoPencil hhigh hr2 hry
  have hquotient := fixedLowQuotientEquationCountProvider_of_candidate
    S selected Gamma (oldGHighDerivativeOrder S) hhigh hj14
      hdegree hagreement hnoPencil
  exact ⟨⟨by simpa only [validity, tf, yf, rf] using validity,
    hterminal, hquotient⟩⟩

end

end ContactOldCoreHighTEquationProvider6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactOldCoreHighTEquationProvider6750Research.terminal_conditions
#print axioms ProximityPrize.SubmissionLower.ContactOldCoreHighTEquationProvider6750Research.terminalDerivativeSeeds_card_le
#print axioms ProximityPrize.SubmissionLower.ContactOldCoreHighTEquationProvider6750Research.highTOldGEquationProvider6750

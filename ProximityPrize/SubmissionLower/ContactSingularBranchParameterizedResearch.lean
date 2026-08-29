import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTightSingularLedgerResearch
import ProximityPrize.SubmissionLower.ContactSingularBranch6600Research
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCountParameterizedResearch

/-! .







 -/

namespace ProximityPrize.SubmissionLower.ContactSingularBranchParameterizedResearch

open scoped Classical BigOperators
open ContactSelectedSeedDecomposition ContactImplicitPairBudgets
open ContactImplicitContactLift ContactSingularAuxiliary
open ContactSingularDegreeBounds ContactInterpolation ContactTranslation
open ContactFactorCaps ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactSingularBranch6600Research
open ContactTightSingularLedgerResearch
open ContactImplicitPairSeedCountParameterizedResearch
open ContactSingularLedger6600Research

noncomputable section

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev TightParameters := ContactTightSingularLedgerResearch.TightParameters

namespace TightParameters

/-- .
 -/
theorem implicitVector_budgets_of_profile
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p) (hw : 1 ≤ P.w) :
    (∑ q : ImplicitIndex Q, (implicitVector Q q).y) ≤ P.algebraicCap ∧
      (∑ q : ImplicitIndex Q, (implicitVector Q q).r) ≤
        2 * P.implicitYCap * P.algebraicCap ∧
      (∑ q : ImplicitIndex Q, (implicitVector Q q).z) ≤ P.implicitYCap := by
  classical
  obtain ⟨hJ, hJboxRaw⟩ := singularAuxiliary_nonzero_mem_box Q
    P.D P.w P.L P.s p hQ hs hsSmall hbox
  have hJbox : singularAuxiliary Q ∈
      globalCoefficientBox K (P.kappa * P.D) P.w P.algebraicCap 0 := by
    simpa [ContactTightSingularLedgerResearch.TightParameters.kappa,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap] using hJboxRaw
  have hb := implicitPair_input_budgets (singularAuxiliary Q) hJ
    (P.kappa * P.D) P.w P.algebraicCap (by omega) hJbox
  simpa only [implicitVector, Finset.sum_coe_sort,
    ContactTightSingularLedgerResearch.TightParameters.implicitYCap] using hb

/-- .
 -/
theorem exceptionalSeeds_bound_of_profile
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hj : 1 ≤ P.algebraicCap)
    (hjSmall : P.algebraicCap < p)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
      2 * P.algebraicCap ^ 2 := by
  classical
  obtain ⟨hJ, hJboxRaw⟩ := singularAuxiliary_nonzero_mem_box Q
    P.D P.w P.L P.s p hQ hs hsSmall hbox
  have hJbox : singularAuxiliary Q ∈
      globalCoefficientBox K (P.kappa * P.D) P.w P.algebraicCap 0 := by
    simpa [ContactTightSingularLedgerResearch.TightParameters.kappa,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap] using hJboxRaw
  have hJR : (singularAuxiliary Q).degreeOf 2 = 0 :=
    Nat.eq_zero_of_le_zero
      (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
  have hJY : (singularAuxiliary Q).degreeOf 1 ≤ P.algebraicCap := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hh := (hJbox hd).1
    omega
  have hJZ : (singularAuxiliary Q).degreeOf 3 ≤ P.algebraicCap :=
    degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
  exact exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR
    P.algebraicCap p hj hjSmall hJY hJZ Gamma selected

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- .
 -/
theorem implicitSeeds_pair_bound_of_profile
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hmixedSmall : 2 * P.implicitYCap * P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors)
    (q : ImplicitIndex Q) :
    (implicitSeeds Q selected Gamma q).card * P.gap ≤
      (P.n - P.w) * dot P.agreement (implicitVector Q q) +
        (P.errors + 1) * P.gap * (implicitVector Q q).z := by
  classical
  obtain ⟨hJ, hJboxRaw⟩ := singularAuxiliary_nonzero_mem_box Q
    P.D P.w P.L P.s p hQ hs hsSmall hbox
  have hJbox : singularAuxiliary Q ∈
      globalCoefficientBox K (P.kappa * P.D) P.w P.algebraicCap 0 := by
    simpa [ContactTightSingularLedgerResearch.TightParameters.kappa,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap] using hJboxRaw
  obtain ⟨_hA, hG, hGR, hAbox, hGbox, hproper⟩ :=
    implicitPair_data (singularAuxiliary Q) hJ
      (P.kappa * P.D) P.w P.algebraicCap hw hDw hJbox q.1 q.2
  have hsub := implicitSeeds_subset Q selected Gamma q
  have hpair := implicit_pair_seed_bound q.1.1 q.1.2 hG hGR hproper
    (P.kappa * P.D) P.w P.implicitYCap P.algebraicCap
    p P.n P.a P.errors hAbox hGbox rfl selected
    (implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
    hw hchar hwa han hjYSmall hjZSmall hmixedSmall
    (fun gamma hgamma => hdegree gamma (hsub hgamma))
    (fun gamma hgamma =>
      (implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
    (fun gamma hgamma =>
      (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
    (fun gamma hgamma =>
      (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
    (fun gamma hgamma => hagreement gamma (hsub hgamma))
    (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors hsub hnoPencil)
  simpa [implicitVector,
    ContactTightSingularLedgerResearch.TightParameters.agreement,
    ContactTightSingularLedgerResearch.TightParameters.errors,
    ContactTightSingularLedgerResearch.TightParameters.gap, dot] using hpair

/-- .
 -/
theorem singularSeeds_tight_gap_bound
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hj : 1 ≤ P.algebraicCap)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hmixedSmall : 2 * P.implicitYCap * P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (singularSeeds Q selected Gamma).card * P.gap ≤ P.tightNumerator := by
  have hcaps := P.implicitVector_budgets_of_profile Q hQ hbox hs hsSmall hw
  have hexc := P.exceptionalSeeds_bound_of_profile Q hQ hbox hs hsSmall
    hj hjZSmall selected Gamma
  have hsum := P.with_exceptions_bound
    (fun q : ImplicitIndex Q => (implicitSeeds Q selected Gamma q).card)
    (implicitVector Q)
    (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
    hcaps.1 hcaps.2.1 hcaps.2.2
    (P.implicitSeeds_pair_bound_of_profile Q hQ hbox hs hsSmall hw hchar
      hDw hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
      hinj hnodes hdegree hagreement hnoPencil)
    hexc
  exact (Nat.mul_le_mul_right P.gap
    (singularSeeds_card_le_sum Q selected Gamma)).trans hsum

/-- . -/
theorem singularSeeds_count_le_countCap
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hj : 1 ≤ P.algebraicCap)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hmixedSmall : 2 * P.implicitYCap * P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (singularSeeds Q selected Gamma).card ≤ P.countCap := by
  apply P.count_le_countCap _ (by
    simpa [ContactTightSingularLedgerResearch.TightParameters.gap] using
      Nat.sub_pos_of_lt hwa)
  exact P.singularSeeds_tight_gap_bound Q hQ hbox hs hsSmall hw hchar hDw
    hj hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
    hinj hnodes hdegree hagreement hnoPencil

end TightParameters

/-! . -/

def firstResidualQ2 : TightParameters :=
  ⟨262144, 131071, 182807, 8591929, 598, 14⟩

def secondResidualGcd12 : TightParameters :=
  ⟨262144, 131071, 182807, 4570175, 598, 7⟩

theorem optimized_pivot_values :
    firstResidualQ2.implicitYCap = 1769 ∧
      firstResidualQ2.algebraicCap = 16146 ∧
      firstResidualQ2.tightNumerator = 2944211023232807391 ∧
      firstResidualQ2.countCap = 56908362131452 ∧
      secondResidualGcd12.implicitYCap = 453 ∧
      secondResidualGcd12.algebraicCap = 7774 ∧
      secondResidualGcd12.tightNumerator = 363014145446108303 ∧
      secondResidualGcd12.countCap = 7016664323606 := by
  norm_num [firstResidualQ2, secondResidualGcd12,
    TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap, dot]

theorem optimized_pivot_characteristic_gates :
    firstResidualQ2.s < 2130706433 ∧
      firstResidualQ2.w < 2130706433 ∧
      firstResidualQ2.implicitYCap < 2130706433 ∧
      firstResidualQ2.algebraicCap < 2130706433 ∧
      2 * firstResidualQ2.implicitYCap * firstResidualQ2.algebraicCap < 2130706433 ∧
      secondResidualGcd12.s < 2130706433 ∧
      secondResidualGcd12.w < 2130706433 ∧
      secondResidualGcd12.implicitYCap < 2130706433 ∧
      secondResidualGcd12.algebraicCap < 2130706433 ∧
      2 * secondResidualGcd12.implicitYCap * secondResidualGcd12.algebraicCap < 2130706433 := by
  norm_num [firstResidualQ2, secondResidualGcd12,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa]

end

end ProximityPrize.SubmissionLower.ContactSingularBranchParameterizedResearch

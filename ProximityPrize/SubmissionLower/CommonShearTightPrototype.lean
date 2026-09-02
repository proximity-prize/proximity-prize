import ProximityPrize.SubmissionLower.AG
import ProximityPrize.SubmissionLower.CommonShearConsumerPrototype

namespace ProximityPrize.SubmissionLower.CommonShearTightPrototype

open scoped Classical BigOperators
open RCN169 RCN167 RCN174 RCN238 RCN243 RCN291 RCN294 RCN318 RCN319

noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type} [Field K]
variable {Iota : Type}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

abbrev TightParameters := RCN318.TightParameters

/-- The only numerical change caused by the common-shear incidence theorem is
the extra `2 * w` coefficient on the aggregate Z cost. -/
def agreement (P : TightParameters) : RCN223.DegreeVector :=
  ⟨1 + 2 * P.w * P.implicitYCap,
    P.w,
    2 * P.w * P.algebraicCap + 1 + 2 * P.w⟩

def coefficients (P : TightParameters) : RCN223.DegreeVector :=
  ⟨(P.n - P.w) * (agreement P).y,
    (P.n - P.w) * (agreement P).r,
    (P.n - P.w) * (agreement P).z + (P.errors + 1) * P.gap⟩

def coreNumerator (P : TightParameters) : ℕ :=
  (P.n - P.w) * RCN294.dot (agreement P) P.aggregateCost +
    (P.errors + 1) * P.gap * P.implicitYCap

def tightNumerator (P : TightParameters) : ℕ :=
  coreNumerator P + 2 * P.algebraicCap ^ 2 * P.gap

def countCap (P : TightParameters) : ℕ := tightNumerator P / P.gap

theorem bound_eq_dot (P : TightParameters) (v : RCN223.DegreeVector) :
    (P.n - P.w) * RCN294.dot (agreement P) v +
        (P.errors + 1) * P.gap * v.z =
      RCN294.dot v (coefficients P) := by
  simp only [agreement, coefficients, RCN318.TightParameters.errors,
    RCN318.TightParameters.gap, RCN294.dot]
  ring

theorem aggregate_eq_core (P : TightParameters) :
    RCN294.dot P.aggregateCost (coefficients P) = coreNumerator P := by
  simp only [agreement, coefficients, coreNumerator,
    RCN318.TightParameters.aggregateCost, RCN318.TightParameters.errors,
    RCN318.TightParameters.gap, RCN294.dot]
  ring

theorem sum_counts_bound (P : TightParameters) {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → RCN223.DegreeVector)
    (hy : (∑ i, (cost i).y) ≤ P.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤
      2 * P.implicitYCap * P.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ P.implicitYCap)
    (hcount : ∀ i, count i * P.gap ≤
      (P.n - P.w) * RCN294.dot (agreement P) (cost i) +
        (P.errors + 1) * P.gap * (cost i).z) :
    (∑ i, count i) * P.gap ≤ coreNumerator P := by
  calc
    (∑ i, count i) * P.gap = ∑ i, count i * P.gap :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ i, RCN294.dot (cost i) (coefficients P) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← bound_eq_dot]
      exact hcount i
    _ = RCN294.dot (RCN294.sumVector cost) (coefficients P) :=
      (RCN294.dot_sum_left cost (coefficients P)).symm
    _ ≤ RCN294.dot P.aggregateCost (coefficients P) :=
      RCN294.dot_mono_left (coefficients P) ⟨hy, hr, hz⟩
    _ = coreNumerator P := aggregate_eq_core P

theorem with_exceptions_bound (P : TightParameters)
    {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → RCN223.DegreeVector)
    (exceptions : ℕ)
    (hy : (∑ i, (cost i).y) ≤ P.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤
      2 * P.implicitYCap * P.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ P.implicitYCap)
    (hcount : ∀ i, count i * P.gap ≤
      (P.n - P.w) * RCN294.dot (agreement P) (cost i) +
        (P.errors + 1) * P.gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * P.algebraicCap ^ 2) :
    ((∑ i, count i) + exceptions) * P.gap ≤ tightNumerator P := by
  have hmain := sum_counts_bound P count cost hy hr hz hcount
  calc
    ((∑ i, count i) + exceptions) * P.gap =
        (∑ i, count i) * P.gap + exceptions * P.gap := Nat.add_mul _ _ _
    _ ≤ coreNumerator P + 2 * P.algebraicCap ^ 2 * P.gap :=
      Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
    _ = tightNumerator P := rfl

theorem count_le_countCap (P : TightParameters) (count : ℕ)
    (hgap : 0 < P.gap) (hcount : count * P.gap ≤ tightNumerator P) :
    count ≤ countCap P := by
  exact (Nat.le_div_iff_mul_le hgap).mpr hcount

theorem implicitSeeds_pair_bound_of_profile
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors)
    (q : RCN291.ImplicitIndex Q) :
    (RCN291.implicitSeeds Q selected Gamma q).card * P.gap ≤
      (P.n - P.w) * RCN294.dot (agreement P) (RCN291.implicitVector Q q) +
        (P.errors + 1) * P.gap * (RCN291.implicitVector Q q).z := by
  classical
  obtain ⟨hJ, hJboxRaw⟩ := RCN293.singularAuxiliary_nonzero_mem_box Q
    P.D P.w P.L P.s p hQ hs hsSmall hbox
  have hJbox : RCN290.singularAuxiliary Q ∈
      globalCoefficientBox K (P.kappa * P.D) P.w P.algebraicCap 0 := by
    simpa [RCN318.TightParameters.kappa,
      RCN318.TightParameters.algebraicCap] using hJboxRaw
  obtain ⟨_hA, hG, hGR, hAbox, hGbox, hproper⟩ :=
    RCN286.implicitPair_data (RCN290.singularAuxiliary Q) hJ
      (P.kappa * P.D) P.w P.algebraicCap hw hDw hJbox q.1 q.2
  have hsub := RCN291.implicitSeeds_subset Q selected Gamma q
  have hpair :=
    CommonShearConsumerPrototype.implicit_pair_seed_bound_common_global_shear
      q.1.1 q.1.2 hG hGR hproper
      (P.kappa * P.D) P.w P.implicitYCap P.algebraicCap
      p P.n P.a P.errors hAbox hGbox rfl selected
      (RCN291.implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
      hw hchar hwa han hjYSmall hjZSmall
      (fun gamma hgamma => hdegree gamma (hsub hgamma))
      (fun gamma hgamma =>
        (RCN291.implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
      (fun gamma hgamma =>
        (RCN291.implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
      (fun gamma hgamma =>
        (RCN291.implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
      (fun gamma hgamma => hagreement gamma (hsub hgamma))
      (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors hsub hnoPencil)
  simpa [RCN291.implicitVector, agreement,
    RCN318.TightParameters.errors, RCN318.TightParameters.gap,
    RCN294.dot] using hpair

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
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (RCN291.singularSeeds Q selected Gamma).card * P.gap ≤
      tightNumerator P := by
  have hcaps := RCN292.TightParameters.implicitVector_budgets_of_profile
    P Q hQ hbox hs hsSmall hw
  have hexc := RCN292.TightParameters.exceptionalSeeds_bound_of_profile
    P Q hQ hbox hs hsSmall hj hjZSmall selected Gamma
  have hsum := with_exceptions_bound P
    (fun q : RCN291.ImplicitIndex Q =>
      (RCN291.implicitSeeds Q selected Gamma q).card)
    (RCN291.implicitVector Q)
    (RCN286.exceptionalSeeds (RCN290.singularAuxiliary Q) Gamma selected).card
    hcaps.1 hcaps.2.1 hcaps.2.2
    (implicitSeeds_pair_bound_of_profile P Q hQ hbox hs hsSmall hw hchar
      hDw hjYSmall hjZSmall hwa han selected Gamma nodes x u0 u1 hinj
      hnodes hdegree hagreement hnoPencil)
    hexc
  exact (Nat.mul_le_mul_right P.gap
    (RCN291.singularSeeds_card_le_sum Q selected Gamma)).trans hsum

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
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (RCN291.singularSeeds Q selected Gamma).card ≤ countCap P := by
  apply count_le_countCap P _ (by
    simpa [RCN318.TightParameters.gap] using Nat.sub_pos_of_lt hwa)
  exact singularSeeds_tight_gap_bound P Q hQ hbox hs hsSmall hw hchar hDw
    hj hjYSmall hjZSmall hwa han selected Gamma nodes x u0 u1 hinj hnodes
    hdegree hagreement hnoPencil

end

end ProximityPrize.SubmissionLower.CommonShearTightPrototype

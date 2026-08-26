import ProximityPrize.SubmissionLower.BCHKSFiniteRankOnePrincipalization6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusWeakCurveSeed6401

/-!
# What many visible shifts really force in the rank-one branch

Suppose a finite family of bivariate polynomial rows is linearly independent
over the challenge ring `F[Z]`, but every row is a polynomial multiple of one
common direction over `F[Z][X]`.  Then the scalar multipliers themselves are
linearly independent over `F[Z]`.  If one nonzero component of every row has
outer `X`-degree at most `d`, the multipliers fit in a free module of rank
`d + 1 - deg_X(direction component)`.  This gives the sharp dimension bound

`card family + deg_X(direction component) <= d + 1`.

At the balanced score-6401 parameters, `10592` visible directions in either
homogeneous component therefore force the common primitive direction to have
`X`-degree at most `33100` in that component.  This is an unconditional
consequence of literal polynomial principalization; it does not turn the
multipliers into boundedly many coefficient profiles and does not assert the
still-missing owner-mass classification.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSShiftedMinimalIndexMultiplierRigidity6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFiniteRankOnePrincipalization6401

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

noncomputable section

/-- The three-row principalization theorem extends without loss to an
arbitrary nonempty finite family: use one base row, remove the gcd of its
three components, and principalize every other row against that same
primitive direction. -/
theorem exists_commonPolynomialDirection_of_pairwiseRankOne_family
    {F I : Type*} [Field F] [Fintype I] [Nonempty I]
    (rows : I → SymbolicRow F)
    (hrows : ∀ i, rows i ≠ 0)
    (hrankOne : ∀ i k,
      ¬ SymbolicRowPairIndependent (rows i) (rows k)) :
    ∃ (direction : SymbolicRow F) (multiplier : I → XOverZ F),
      direction ≠ 0 ∧
      (∀ i, multiplier i ≠ 0) ∧
      ∀ i j, rows i j = multiplier i * direction j := by
  classical
  letI : NormalizedGCDMonoid (XOverZ F) :=
    Classical.choice
      (inferInstance : Nonempty (NormalizedGCDMonoid (XOverZ F)))
  let base : I := Classical.choice inferInstance
  obtain ⟨direction, hbaseFactor, hgcd⟩ :=
    Finset.extract_gcd (rows base)
      (s := (Finset.univ : Finset (Fin 3))) Finset.univ_nonempty
  let G : XOverZ F :=
    (Finset.univ : Finset (Fin 3)).gcd (rows base)
  have hGne : G ≠ 0 := by
    intro hGzero
    apply hrows base
    funext j
    simpa [G, hGzero] using hbaseFactor j (Finset.mem_univ j)
  have hdirection : direction ≠ 0 := by
    intro hzero
    apply hrows base
    funext j
    simpa [G, hzero] using hbaseFactor j (Finset.mem_univ j)
  have hcrossDirection : ∀ i j k,
      direction j * rows i k = rows i j * direction k := by
    intro i j k
    have hpair := hrankOne base i
    have h01 : symbolicMinor01 (rows base) (rows i) = 0 :=
      not_ne_iff.mp (fun h ↦ hpair (Or.inl h))
    have h02 : symbolicRankTwoNumerator (rows base) (rows i) = 0 :=
      not_ne_iff.mp (fun h ↦ hpair (Or.inr (Or.inl h)))
    have h12 : symbolicRankTwoDenominator (rows base) (rows i) = 0 :=
      not_ne_iff.mp (fun h ↦ hpair (Or.inr (Or.inr h)))
    have hrowCross : rows base j * rows i k =
        rows i j * rows base k := by
      fin_cases j <;> fin_cases k
      · exact mul_comm _ _
      · exact sub_eq_zero.mp h01
      · exact sub_eq_zero.mp h02
      · calc
          rows base 1 * rows i 0 = rows i 0 * rows base 1 := mul_comm _ _
          _ = rows base 0 * rows i 1 := (sub_eq_zero.mp h01).symm
          _ = rows i 1 * rows base 0 := mul_comm _ _
      · exact mul_comm _ _
      · exact sub_eq_zero.mp h12
      · calc
          rows base 2 * rows i 0 = rows i 0 * rows base 2 := mul_comm _ _
          _ = rows base 0 * rows i 2 := (sub_eq_zero.mp h02).symm
          _ = rows i 2 * rows base 0 := mul_comm _ _
      · calc
          rows base 2 * rows i 1 = rows i 1 * rows base 2 := mul_comm _ _
          _ = rows base 1 * rows i 2 := (sub_eq_zero.mp h12).symm
          _ = rows i 2 * rows base 1 := mul_comm _ _
      · exact mul_comm _ _
    have hj := hbaseFactor j (Finset.mem_univ j)
    have hk := hbaseFactor k (Finset.mem_univ k)
    apply mul_left_cancel₀ hGne
    calc
      G * (direction j * rows i k) =
          (G * direction j) * rows i k := by rw [mul_assoc]
      _ = rows base j * rows i k := by rw [← hj]
      _ = rows i j * rows base k := hrowCross
      _ = rows i j * (G * direction k) := by rw [hk]
      _ = G * (rows i j * direction k) := by ac_rfl
  have hm : ∀ i, ∃ m : XOverZ F,
      m ≠ 0 ∧ ∀ j, rows i j = m * direction j := by
    intro i
    exact exists_polynomial_multiplier_of_gcd_one direction (rows i)
      hdirection (hrows i) hgcd (hcrossDirection i)
  choose multiplier hmne hfactor using hm
  exact ⟨direction, multiplier, hdirection, hmne, hfactor⟩

/-- Multiplication by one fixed polynomial row, viewed as a linear map over
the coefficient/challenge ring. -/
def commonDirectionScaleLinearMap
    {F J : Type*} [Field F] (direction : J → XOverZ F) :
    XOverZ F →ₗ[F[X]] (J → XOverZ F) where
  toFun m j := m * direction j
  map_add' m n := by
    funext j
    simp [add_mul]
  map_smul' c m := by
    funext j
    simp [Algebra.smul_def, mul_assoc]

/-- Linear independence of literal common-direction rows descends to their
scalar polynomial multipliers.  No bounded-coefficient or primitivity
assumption on the multipliers is used. -/
theorem multipliers_linearIndependent_of_rows
    {F I J : Type*} [Field F]
    (rows : I → J → XOverZ F)
    (direction : J → XOverZ F) (multiplier : I → XOverZ F)
    (hfactor : ∀ i j, rows i j = multiplier i * direction j)
    (hrows : LinearIndependent F[X] rows) :
    LinearIndependent F[X] multiplier := by
  apply LinearIndependent.of_comp (commonDirectionScaleLinearMap direction)
  have heq :
      commonDirectionScaleLinearMap direction ∘ multiplier = rows := by
    funext i j
    exact (hfactor i j).symm
  rwa [heq]

/-- Complete finite-family algebraic endpoint: pairwise rank one plus
linear independence yields one literal common polynomial direction and a
linearly independent multiplier family. -/
theorem exists_commonDirection_independentMultipliers
    {F I : Type*} [Field F] [Fintype I] [Nonempty I]
    (rows : I → SymbolicRow F)
    (hrows : LinearIndependent F[X] rows)
    (hrankOne : ∀ i k,
      ¬ SymbolicRowPairIndependent (rows i) (rows k)) :
    ∃ (direction : SymbolicRow F) (multiplier : I → XOverZ F),
      direction ≠ 0 ∧
      (∀ i, multiplier i ≠ 0) ∧
      LinearIndependent F[X] multiplier ∧
      ∀ i j, rows i j = multiplier i * direction j := by
  obtain ⟨direction, multiplier, hdirection, hmne, hfactor⟩ :=
    exists_commonPolynomialDirection_of_pairwiseRankOne_family rows
      hrows.ne_zero hrankOne
  exact ⟨direction, multiplier, hdirection, hmne,
    multipliers_linearIndependent_of_rows rows direction multiplier
      hfactor hrows,
    hfactor⟩

private theorem mem_degreeLT_of_natDegree_le
    {R : Type*} [Semiring R] (Q : R[X]) (d : Nat)
    (hQ : Q.natDegree ≤ d) :
    Q ∈ Polynomial.degreeLT R (d + 1) := by
  by_cases hzero : Q = 0
  · simp [hzero]
  · rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hzero]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hQ)

/-- Over any coefficient ring satisfying the strong rank condition, an
independent finite family of polynomials of degree at most `d` has at most
`d+1` members. -/
theorem card_le_degree_add_one_of_polynomial_linearIndependent
    {R I : Type*} [CommRing R] [StrongRankCondition R] [Fintype I]
    (m : I → R[X]) (hm : LinearIndependent R m) (d : Nat)
    (hdegree : ∀ i, (m i).natDegree ≤ d) :
    Fintype.card I ≤ d + 1 := by
  let bounded : I → Polynomial.degreeLT R (d + 1) :=
    fun i ↦ ⟨m i, mem_degreeLT_of_natDegree_le (m i) d (hdegree i)⟩
  have hbounded : LinearIndependent R bounded := by
    apply LinearIndependent.of_comp
      (Submodule.subtype (Polynomial.degreeLT R (d + 1)))
    simpa [bounded, Function.comp_def] using hm
  simpa using
    (Polynomial.degreeLT.basis R (d + 1)).card_le_card_of_linearIndependent
      hbounded

/-- The exact two-axis room inequality.  A nonzero common-direction
component consumes its own `X`-degree in every row, while independent
multipliers consume one remaining coefficient slot each. -/
theorem card_add_directionDegree_le_rowSlots
    {F I J : Type*} [Field F] [Fintype I] [Nonempty I]
    (rows : I → J → XOverZ F)
    (direction : J → XOverZ F) (multiplier : I → XOverZ F)
    (hfactor : ∀ i j, rows i j = multiplier i * direction j)
    (hrows : LinearIndependent F[X] rows)
    (pivot : J) (hpivot : direction pivot ≠ 0) (d : Nat)
    (hrowDegree : ∀ i, (rows i pivot).natDegree ≤ d) :
    Fintype.card I + (direction pivot).natDegree ≤ d + 1 := by
  have hmLI : LinearIndependent F[X] multiplier :=
    multipliers_linearIndependent_of_rows rows direction multiplier
      hfactor hrows
  have hmne : ∀ i, multiplier i ≠ 0 := hmLI.ne_zero
  let i0 : I := Classical.choice inferInstance
  have hpivotDegree : (direction pivot).natDegree ≤ d := by
    have h := hrowDegree i0
    rw [hfactor, Polynomial.natDegree_mul (hmne i0) hpivot] at h
    omega
  have hmDegree : ∀ i,
      (multiplier i).natDegree ≤ d - (direction pivot).natDegree := by
    intro i
    have h := hrowDegree i
    rw [hfactor, Polynomial.natDegree_mul (hmne i) hpivot] at h
    omega
  have hcard : Fintype.card I ≤
      (d - (direction pivot).natDegree) + 1 :=
    card_le_degree_add_one_of_polynomial_linearIndependent multiplier hmLI
      (d - (direction pivot).natDegree) hmDegree
  omega

/-- Instantiation of the exact dimension inequality in the balanced source
box.  This is the new `X`-degree information supplied by the `10592`
visible directions. -/
theorem balanced10592_direction_component_degree_le_33100
    {F J : Type*} [Field F]
    (rows : Fin 10592 → J → XOverZ F)
    (direction : J → XOverZ F)
    (multiplier : Fin 10592 → XOverZ F)
    (hfactor : ∀ i j, rows i j = multiplier i * direction j)
    (hrows : LinearIndependent F[X] rows)
    (pivot : J) (hpivot : direction pivot ≠ 0)
    (hrowDegree : ∀ i, (rows i pivot).natDegree ≤
      a1XSlots6401 - 1) :
    (direction pivot).natDegree ≤ 33100 := by
  have h := card_add_directionDegree_le_rowSlots rows direction multiplier
    hfactor hrows pivot hpivot (a1XSlots6401 - 1) hrowDegree
  norm_num [a1XSlots6401] at h ⊢
  omega

/-- Pure average-index payoff after the common-direction factorization.
Every visible row has shifted degree at least the primitive direction's
shifted degree, so `10592` rows and the total budget `Delta` force the
advertised strict `< 5q` bound. -/
theorem primitiveIndex_le_8789164040_of_10592_visible
    (primitiveIndex : Nat) (rowIndex : Fin 10592 → Nat)
    (hlower : ∀ i, primitiveIndex ≤ rowIndex i)
    (hsum : ∑ i, rowIndex i ≤ moduleIndexSum6401) :
    primitiveIndex ≤ 8789164040 := by
  have hmul : 10592 * primitiveIndex ≤ ∑ i, rowIndex i := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _hi ↦ hlower i)
  have hbudget : 10592 * primitiveIndex ≤ moduleIndexSum6401 :=
    hmul.trans hsum
  norm_num [moduleIndexSum6401, a1XSlots6401, q6401] at hbudget ⊢
  omega

theorem primitiveIndex_8789164040_lt_five_q6401 :
    8789164040 < 5 * q6401 := by
  norm_num [q6401]

/-! ## Why naive six-orbit expansion does not consume the owner mass -/

/-- Expanding a degree-`8789164040` coefficient through five successive
Frobenius substitutions pays the geometric factor
`1 + q + q^2 + q^3 + q^4`.  This is the direct graph-degree cap of the
naive norm/Hilbert--90 expansion, before any cancellation theorem. -/
def naiveFiveFrobeniusExpansionCap6401 : Nat :=
  8789164040 * (1 + q6401 + q6401 ^ 2 + q6401 ^ 3 + q6401 ^ 4)

/-- Largest per-profile graph degree for which `210` direct source-incidence
charges can still fit strictly below the weak-seed owner mass. -/
def twoHundredTenGraphDegreeBudget6401 : Nat := 269778134916865

/-- Exact scale separation.  Direct bounded graphs at the displayed budget
would consume the mass, but the automatic five-Frobenius expansion is over
thirty orders of magnitude too large.  Therefore a useful consumer needs a
digit-preserving/cancellation theorem; ordinary norm expansion is not it. -/
theorem naiveFiveFrobeniusExpansion_misses_massBudget6401 :
    a6401 - ownerDegreeCap6401 = 54283 ∧
      naiveFiveFrobeniusExpansionCap6401 =
        181151543487315326812670368541016211690828595240 ∧
      210 * n6401 * twoHundredTenGraphDegreeBudget6401 <
        weakCurveSeedInput6401 * (a6401 - ownerDegreeCap6401) ∧
      weakCurveSeedInput6401 * (a6401 - ownerDegreeCap6401) ≤
        210 * n6401 * (twoHundredTenGraphDegreeBudget6401 + 1) ∧
      twoHundredTenGraphDegreeBudget6401 <
        naiveFiveFrobeniusExpansionCap6401 := by
  native_decide

end

end BCHKSShiftedMinimalIndexMultiplierRigidity6401
end ProximityPrize.SubmissionLower

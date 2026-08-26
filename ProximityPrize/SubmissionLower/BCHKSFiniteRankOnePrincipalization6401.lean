import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusThreeShiftPrimitive6401

/-!
# Finite rank-one rows have a common polynomial direction

For three nonzero rows over `F[Z][X]`, pairwise vanishing of all exterior
coordinates gives rational proportionality.  This file proves the stronger
integral statement needed by the extreme-rectangle producer: all rows are
literal nonzero polynomial multiples of one common row.

The proof extracts the finite gcd of the three components of one base row.
The quotient direction has gcd one.  Cross multiplication then makes a
nonzero pivot divide the pivot of every other row: it divides each product
of that pivot with a direction component, hence their finite gcd, which is
associated to the pivot itself.  No Bezout or principal-ideal hypothesis is
used.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFiniteRankOnePrincipalization6401

open Polynomial
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-- A nonzero three-component row has a component which can be used as a
division-free pivot. -/
theorem exists_nonzero_component
    {F : Type*} [Field F] (d : SymbolicRow F) (hd : d ≠ 0) :
    ∃ p : Fin 3, d p ≠ 0 := by
  by_contra h
  apply hd
  funext p
  by_contra hp
  exact h ⟨p, hp⟩

/-- A primitive row controls every row cross-proportional to it. -/
theorem exists_polynomial_multiplier_of_gcd_one
    {F : Type*} [Field F] [NormalizedGCDMonoid (XOverZ F)]
    (d r : SymbolicRow F)
    (hd : d ≠ 0)
    (hr : r ≠ 0)
    (hgcd : (Finset.univ : Finset (Fin 3)).gcd d = 1)
    (hcross : ∀ j k, d j * r k = r j * d k) :
    ∃ m : XOverZ F, m ≠ 0 ∧ ∀ j, r j = m * d j := by
  classical
  obtain ⟨p, hp⟩ := exists_nonzero_component d hd
  have hpDvdEach : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      d p ∣ r p * d j := by
    intro j _hj
    exact ⟨r j, (hcross p j).symm⟩
  have hpDvdGcd :
      d p ∣ (Finset.univ : Finset (Fin 3)).gcd
        (fun j => r p * d j) := by
    exact Finset.dvd_gcd hpDvdEach
  have hassociated : Associated
      ((Finset.univ : Finset (Fin 3)).gcd (fun j => r p * d j))
      (r p * (Finset.univ : Finset (Fin 3)).gcd d) :=
    Finset.gcd_mul_left' (Finset.univ : Finset (Fin 3)) d (r p)
  have hpDvd : d p ∣ r p := by
    have h := hpDvdGcd.trans hassociated.dvd
    rw [hgcd, mul_one] at h
    exact h
  obtain ⟨m, hm⟩ := hpDvd
  have hfactor : ∀ j, r j = m * d j := by
    intro j
    apply mul_left_cancel₀ hp
    calc
      d p * r j = r p * d j := hcross p j
      _ = (d p * m) * d j := by rw [hm]
      _ = d p * (m * d j) := by rw [mul_assoc]
  have hmne : m ≠ 0 := by
    intro hmzero
    apply hr
    funext j
    simpa [hmzero] using hfactor j
  exact ⟨m, hmne, hfactor⟩

/-- Pairwise rank-one rows over the bivariate polynomial UFD have one
literal common polynomial direction and nonzero polynomial multipliers. -/
theorem exists_commonPolynomialDirection_of_pairwiseRankOne
    {F : Type*} [Field F]
    (rows : Fin 3 → SymbolicRow F)
    (hrows : ∀ s, rows s ≠ 0)
    (hrankOne : ∀ s t, ¬ SymbolicRowPairIndependent (rows s) (rows t)) :
    ∃ (direction : SymbolicRow F) (multiplier : Fin 3 → XOverZ F),
      direction ≠ 0 ∧
      (∀ s, multiplier s ≠ 0) ∧
      ∀ s j, rows s j = multiplier s * direction j := by
  classical
  letI : NormalizedGCDMonoid (XOverZ F) :=
    Classical.choice
      (inferInstance : Nonempty (NormalizedGCDMonoid (XOverZ F)))
  obtain ⟨direction, hbaseFactor, hgcd⟩ :=
    Finset.extract_gcd (rows 0)
      (s := (Finset.univ : Finset (Fin 3))) Finset.univ_nonempty
  let G : XOverZ F := (Finset.univ : Finset (Fin 3)).gcd (rows 0)
  have hGne : G ≠ 0 := by
    intro hGzero
    apply hrows 0
    funext j
    simpa [G, hGzero] using hbaseFactor j (Finset.mem_univ j)
  have hdne : direction ≠ 0 := by
    intro hdzero
    apply hrows 0
    funext j
    simpa [G, hdzero] using hbaseFactor j (Finset.mem_univ j)
  have hcrossDirection : ∀ s j k,
      direction j * rows s k = rows s j * direction k := by
    intro s j k
    have hpair := hrankOne 0 s
    have h01 : symbolicMinor01 (rows 0) (rows s) = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inl h))
    have h02 : symbolicRankTwoNumerator (rows 0) (rows s) = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inr (Or.inl h)))
    have h12 : symbolicRankTwoDenominator (rows 0) (rows s) = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inr (Or.inr h)))
    have hrowCross : rows 0 j * rows s k = rows s j * rows 0 k := by
      fin_cases j <;> fin_cases k
      · exact mul_comm _ _
      · exact sub_eq_zero.mp h01
      · exact sub_eq_zero.mp h02
      · calc
          rows 0 1 * rows s 0 = rows s 0 * rows 0 1 := mul_comm _ _
          _ = rows 0 0 * rows s 1 := (sub_eq_zero.mp h01).symm
          _ = rows s 1 * rows 0 0 := mul_comm _ _
      · exact mul_comm _ _
      · exact sub_eq_zero.mp h12
      · calc
          rows 0 2 * rows s 0 = rows s 0 * rows 0 2 := mul_comm _ _
          _ = rows 0 0 * rows s 2 := (sub_eq_zero.mp h02).symm
          _ = rows s 2 * rows 0 0 := mul_comm _ _
      · calc
          rows 0 2 * rows s 1 = rows s 1 * rows 0 2 := mul_comm _ _
          _ = rows 0 1 * rows s 2 := (sub_eq_zero.mp h12).symm
          _ = rows s 2 * rows 0 1 := mul_comm _ _
      · exact mul_comm _ _
    have hj := hbaseFactor j (Finset.mem_univ j)
    have hk := hbaseFactor k (Finset.mem_univ k)
    apply mul_left_cancel₀ hGne
    calc
      G * (direction j * rows s k) =
          (G * direction j) * rows s k := by rw [mul_assoc]
      _ = rows 0 j * rows s k := by rw [← hj]
      _ = rows s j * rows 0 k := hrowCross
      _ = rows s j * (G * direction k) := by rw [hk]
      _ = G * (rows s j * direction k) := by ac_rfl
  have hm : ∀ s, ∃ m : XOverZ F,
      m ≠ 0 ∧ ∀ j, rows s j = m * direction j := by
    intro s
    exact exists_polynomial_multiplier_of_gcd_one direction (rows s)
      hdne (hrows s) hgcd (hcrossDirection s)
  choose multiplier hmne hfactor using hm
  exact ⟨direction, multiplier, hdne, hmne, hfactor⟩

/-- The algebraic principalization packages directly into the exact
three-shift structure once the source row caps are available. -/
theorem exists_threeShiftCommonDirection_of_pairwiseRankOne
    {F : Type*} [Field F]
    (rows : Fin 3 → SymbolicRow F)
    (hrows : ∀ s, rows s ≠ 0)
    (hcaps : ∀ s j, (rows s j).natDegree ≤ threeShiftRowXCap6401 s j)
    (hrankOne : ∀ s t, ¬ SymbolicRowPairIndependent (rows s) (rows t)) :
    Nonempty (ThreeShiftCommonDirection (F := F)) := by
  classical
  obtain ⟨direction, multiplier, hdirection, hmultiplier, hfactor⟩ :=
    exists_commonPolynomialDirection_of_pairwiseRankOne rows hrows hrankOne
  exact ⟨{
    rows := rows
    direction := direction
    multiplier := multiplier
    multiplier_ne_zero := hmultiplier
    row_factor := hfactor
    row_caps := hcaps
    direction_nonzero := hdirection
  }⟩

end BCHKSFiniteRankOnePrincipalization6401
end ProximityPrize.SubmissionLower

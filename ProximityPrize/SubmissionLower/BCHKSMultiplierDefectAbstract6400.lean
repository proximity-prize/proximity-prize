import ProximityPrize.SubmissionLower.BCHKSLagrangeFixedMap6400
import ProximityPrize.SubmissionLower.BCHKSReedSolomonCofactor6400

/-!
# Common nodal defects in a rank-one multiplier family

This file isolates two small algebraic facts used by the score-64 rank-one
search.

* A putative affine lane which agrees with a multiplier product away from a
  fixed set is exactly that product when both degrees fit below the number of
  remaining nodes.
* If an independent family of bounded-degree multipliers all vanish on the
  same nodal set, the size of that set and the family dimension share one
  common degree budget.

The statements are independent of the production field and locator matrix.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSMultiplierDefectAbstract6400

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- Equality on every node outside `Fixed` determines two polynomials whose
degrees are both below the number of those remaining nodes. -/
theorem polynomial_eq_mul_of_eval_eq_outside
    {F I : Type} [Field F] [Fintype I] [DecidableEq I]
    (alpha : I ↪ F) (Fixed : Finset I) (C M Q : F[X])
    (hCdegree : C.natDegree < Fintype.card I - Fixed.card)
    (hMQdegree : (M * Q).natDegree < Fintype.card I - Fixed.card)
    (heval : ∀ i, i ∉ Fixed →
      C.eval (alpha i) = (M * Q).eval (alpha i)) :
    C = M * Q := by
  classical
  let Roots : Finset F :=
    ((Finset.univ : Finset I) \ Fixed).map alpha
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' C (M * Q) Roots
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact heval i (Finset.mem_sdiff.mp hi).2
  · have hcard : Roots.card = Fintype.card I - Fixed.card := by
      simp only [Roots, Finset.card_map, Finset.card_sdiff,
        Finset.card_univ, Finset.inter_univ]
    rw [hcard]
    exact max_lt hCdegree hMQdegree

/-- The subset of fixed nodes where the common quotient does not itself
vanish.  At precisely these nodes a product root forces the multiplier to
vanish. -/
noncomputable def effectiveNodalDefect
    {F I : Type} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (Fixed : Finset I) (K : F[X]) : Finset I :=
  by
    classical
    exact Fixed.filter fun i ↦ K.eval (alpha i) ≠ 0

@[simp]
theorem mem_effectiveNodalDefect
    {F I : Type} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (Fixed : Finset I) (K : F[X]) (i : I) :
    i ∈ effectiveNodalDefect alpha Fixed K ↔
      i ∈ Fixed ∧ K.eval (alpha i) ≠ 0 := by
  classical
  simp only [effectiveNodalDefect, Finset.mem_filter]

/-- If `M*K` vanishes at every fixed node, then `M` contains the locator of
the effective nodes, namely those where `K` is nonzero. -/
theorem effectiveNodalLocator_dvd_multiplier
    {F I : Type} [Field F] [Fintype I] [DecidableEq I]
    (alpha : I ↪ F) (Fixed : Finset I) (K M : F[X])
    (hroot : ∀ i ∈ Fixed, (M * K).eval (alpha i) = 0) :
    Lagrange.nodal (effectiveNodalDefect alpha Fixed K)
        (fun i ↦ alpha i) ∣ M := by
  classical
  rw [show Lagrange.nodal (effectiveNodalDefect alpha Fixed K)
      (fun i ↦ alpha i) =
        outsideAgreementLocator alpha
          (effectiveNodalDefect alpha Fixed K) ∅ by
    simp only [outsideAgreementLocator, Finset.sdiff_empty]]
  apply outsideAgreementLocator_dvd
  intro i hi _hiEmpty
  have hi' := (mem_effectiveNodalDefect alpha Fixed K i).mp hi
  have hproduct := hroot i hi'.1
  rw [Polynomial.eval_mul] at hproduct
  exact (mul_eq_zero.mp hproduct).resolve_right hi'.2

/-- An independent family of degree-`<t` polynomials cannot all contain a
common nonzero factor of degree `d` unless `card family + d <= t`. -/
theorem card_add_natDegree_le_of_linearIndependent_dvd
    {F J : Type} [Field F] [Fintype J] [Nonempty J]
    (family : J → F[X]) (R : F[X]) (t : Nat)
    (hLI : LinearIndependent F family) (hR : R ≠ 0)
    (hdegree : ∀ j, (family j).natDegree < t)
    (hdiv : ∀ j, R ∣ family j) :
    Fintype.card J + R.natDegree ≤ t := by
  classical
  let quotient : J → F[X] := fun j ↦ Classical.choose (hdiv j)
  have hfactor : ∀ j, family j = R * quotient j := by
    intro j
    exact Classical.choose_spec (hdiv j)
  have hfamilyNe : ∀ j, family j ≠ 0 := hLI.ne_zero
  have hquotientNe : ∀ j, quotient j ≠ 0 := by
    intro j hzero
    apply hfamilyNe j
    rw [hfactor j, hzero, mul_zero]
  let j₀ : J := Classical.choice (inferInstance : Nonempty J)
  have hRdegreeLt : R.natDegree < t := by
    have hdegreeEq := congrArg Polynomial.natDegree (hfactor j₀)
    rw [Polynomial.natDegree_mul hR (hquotientNe j₀)] at hdegreeEq
    have hj := hdegree j₀
    omega
  have hquotientLI : LinearIndependent F quotient := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    apply (Fintype.linearIndependent_iff.mp hLI c) ?_
    calc
      (∑ i, c i • family i) =
          ∑ i, c i • (R * quotient i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hfactor i]
      _ = R * (∑ i, c i • quotient i) := by
            simp only [smul_eq_C_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = 0 := by rw [hc, mul_zero]
  have hquotientDegree : ∀ j,
      (quotient j).natDegree < t - R.natDegree := by
    intro j
    have hdegreeEq := congrArg Polynomial.natDegree (hfactor j)
    rw [Polynomial.natDegree_mul hR (hquotientNe j)] at hdegreeEq
    have hsum : R.natDegree + (quotient j).natDegree < t := by
      rw [← hdegreeEq]
      exact hdegree j
    omega
  let bounded : J → Polynomial.degreeLT F (t - R.natDegree) :=
    fun j ↦ ⟨quotient j,
      Polynomial.mem_degreeLT.mpr <|
        (Polynomial.natDegree_lt_iff_degree_lt (hquotientNe j)).mp
          (hquotientDegree j)⟩
  have hboundedLI : LinearIndependent F bounded := by
    apply LinearIndependent.of_comp
      (Polynomial.degreeLT F (t - R.natDegree)).subtype
    change LinearIndependent F quotient
    exact hquotientLI
  have hcard := hboundedLI.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis
    (Polynomial.degreeLT.basis F (t - R.natDegree))] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

end BCHKSMultiplierDefectAbstract6400
end ProximityPrize.SubmissionLower

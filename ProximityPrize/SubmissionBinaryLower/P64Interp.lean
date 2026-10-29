import ProximityPrize.SubmissionBinaryLower.P64GSGeneric
import ProximityPrize.SubmissionBinaryLower.P64AffineSum

/-!
# Lemma E and Lemma GS at the 64.00 parameters (PROOF.md 2.1, 2.3)

Parameters: `n = 2^21`, `k = D = 1048575`, `m = 249292`, `DX = mA = 369677849012`,
`DY = J = 352553`, `DZ = 58589180686`. The two index-set cardinalities are computed in closed
form (`six_mul_sum_range`), not by evaluation:

- `6·#unknowns = 6·Σ_{j<J} (mA - Dj)(DZ - j) = 22907959062286402080402927960`,
- `6·#equations = 6·n·Σ_{t<m} (m - t)(DZ - t) = 22907959062286401857812168704`,

with difference `6·37098459876` (PROOF.md Lemma E).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Interp

open Polynomial P64GS P64LineOrder BCHKSSubstitutionVanish

/-- The interpolation parameters. -/
def gsParams : GSParams :=
  ⟨2097152, 1048575, fun _ => 249292, 369677849012, 352553, 58589180686,
    fun _ => by norm_num, by norm_num, by norm_num⟩

theorem six_card_var :
    6 * (Fintype.card (VarIndex gsParams) : ℤ) = 22907959062286402080402927960 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => (gsParams.DX - gsParams.k * j) * (gsParams.DZ - j))]
  push_cast
  have hterm : ∀ j ∈ Finset.range 352553,
      ((369677849012 - 1048575 * j : ℕ) : ℤ) * ((58589180686 - j : ℕ) : ℤ) =
        (369677849012 - 1048575 * (j : ℤ)) * (58589180686 - 1 * (j : ℤ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [gsParams]
  rw [Finset.sum_congr rfl hterm, six_mul_sum_range]
  norm_num

theorem six_card_con :
    6 * (Fintype.card (ConIndex gsParams) : ℤ) = 22907959062286401857812168704 := by
  rw [card_conIndex_const gsParams 249292 (fun _ => rfl)]
  push_cast
  have hterm : ∀ t ∈ Finset.range 249292,
      ((249292 - t : ℕ) : ℤ) * ((58589180686 - t : ℕ) : ℤ) =
        (249292 - 1 * (t : ℤ)) * (58589180686 - 1 * (t : ℤ)) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [gsParams]
  rw [mul_left_comm, Finset.sum_congr rfl hterm, six_mul_sum_range]
  norm_num

theorem card_con_lt_var : Fintype.card (ConIndex gsParams) < Fintype.card (VarIndex gsParams) := by
  have h1 := six_card_var
  have h2 := six_card_con
  have : (Fintype.card (ConIndex gsParams) : ℤ) < Fintype.card (VarIndex gsParams) := by
    linarith
  exact_mod_cast this

/-- The degree caps of Lemma E in the form used downstream. -/
structure GSCaps {F : Type*} [Field F] (Q : Polynomial (Polynomial (Polynomial F))) : Prop where
  ne_zero : Q ≠ 0
  natDegree_le : Q.natDegree ≤ 352552
  yz_le : P64Caps.YZ.yzSupportDegree Q 1 ≤ 58589180685
  weighted_lt : P64Caps.Weighted.weightedSupportDegree Q 1048575 + 1 ≤ 249292 * 1482911

theorem gsCaps_of_support {F : Type*} [Field F] (Q : Polynomial (Polynomial (Polynomial F)))
    (hQ : Q ≠ 0)
    (hcaps : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      j < 352553 ∧ a + 1048575 * j < 369677849012 ∧
        ((Q.coeff j).coeff a).natDegree + j < 58589180686) : GSCaps Q := by
  have hcoeff : ∀ j, Q.coeff j ≠ 0 → ∃ a, (Q.coeff j).coeff a ≠ 0 := fun j hj =>
    ⟨(Q.coeff j).natDegree, by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hj⟩
  refine ⟨hQ, ?_, ?_, ?_⟩
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_contra hne
    obtain ⟨a, ha⟩ := hcoeff j hne
    have := (hcaps j a ha).1
    omega
  · unfold P64Caps.YZ.yzSupportDegree
    apply Finset.sup_le
    intro j hj
    have hj0 : Q.coeff j ≠ 0 := mem_support_iff.mp hj
    have hdeg : Polynomial.Bivariate.degreeX (Q.coeff j) + j ≤ 58589180685 := by
      have : Polynomial.Bivariate.degreeX (Q.coeff j) ≤ 58589180685 - j := by
        unfold Polynomial.Bivariate.degreeX
        apply Finset.sup_le
        intro a ha
        have := (hcaps j a (mem_support_iff.mp ha)).2.2
        omega
      obtain ⟨a, ha⟩ := hcoeff j hj0
      have := (hcaps j a ha).2.2
      omega
    simpa using hdeg
  · have := P64Caps.Weighted.weightedSupportDegree_lt_of_coeff_cap Q 1048575 369677849012 hQ
      (fun j a ha => (hcaps j a ha).2.1)
    norm_num
    omega

/-- **Lemma E.** A nonzero interpolant with the degree caps, of order at least `m` along every
line `X = ω i, Y = u0 i + Z·u1 i`. -/
theorem exists_interpolant {F : Type} [Field F] (ω : Fin 2097152 ↪ F)
    (u₀ u₁ : Fin 2097152 → F) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), GSCaps Q ∧
      ∀ i, OrdGE Q (ω i) (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) 249292 := by
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    exists_interpolant_gen (p := gsParams) card_con_lt_var ω u₀ u₁
  exact ⟨Q, gsCaps_of_support Q hQ hcaps, fun i a b hab => hvan i a b hab⟩

/-- **Lemma GS.** Every bad curve lies on the interpolant: a codeword `P` of degree at most `D`
agreeing with the line values at `A` of the points kills `Q(X, P(X), z)`. -/
theorem triEval_eq_zero {F ι : Type*} [Field F] [DecidableEq F] (ω : ι ↪ F) (y : ι → F[X])
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : GSCaps Q)
    (hGS : ∀ i, OrdGE Q (ω i) (y i) 249292) (z : F) (P : F[X]) (hP : P.natDegree ≤ 1048575)
    (Az : Finset ι) (hAz : 1482911 ≤ Az.card) (hmatch : ∀ i ∈ Az, P.eval (ω i) = (y i).eval z) :
    triEval Q z P = 0 := by
  classical
  by_contra hne
  have hmult : ∀ i ∈ Az, 249292 ≤ (triEval Q z P).rootMultiplicity (ω i) := fun i hi =>
    le_rootMultiplicity_triEval Q (ω i) z (y i) P _ (hGS i) (hmatch i hi) hne
  have hsum := (Finset.sum_le_sum hmult).trans
    ((P64Cofactor.sum_rootMultiplicity_le_natDegree _ ω Az).trans
      (P64Cofactor.natDegree_triEval_le Q z P 1048575 hP))
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have := hQ.weighted_lt
  nlinarith

end P64Interp
end ProximityPrize.SubmissionBinaryLower

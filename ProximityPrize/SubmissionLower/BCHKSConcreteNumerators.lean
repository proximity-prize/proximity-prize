import ProximityPrize.SubmissionLower.BCHKSFunctionField
import ProximityPrize.SubmissionLower.BCHKSLifts
import ProximityPrize.SubmissionLower.BCHKSHenselSetup
import ProximityPrize.SubmissionLower.BCHKSRationalRootVanishing
import ProximityPrize.SubmissionLower.BCHKSFiniteHensel
import ProximityPrize.SubmissionLower.BCHKSHenselWeight

open Polynomial Polynomial.Bivariate ToRatFunc Ideal
open ProximityPrize.SubmissionLower

namespace RationalFunctions
namespace HenselNumerators
namespace ConcreteFiniteNumerators

noncomputable section

variable {F : Type} [Field F]
variable {R : F[X][X][Y]} {H : F[X][Y]}
  [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

abbrev L := 𝕃 H

/-- A coefficientwise Y/Z degree cap: the Z-degree of the Y^i coefficient,
plus i, is at most D. -/
def YZCap (R : F[X][X][Y]) (D : ℕ) : Prop :=
  ∀ i a, (R.coeff i).coeff a ≠ 0 →
    ((R.coeff i).coeff a).natDegree + i ≤ D

noncomputable def liftedR : (𝕃 H)[X][Y] :=
  R.map (Polynomial.mapRingHom (liftToFunctionField (H := H)))

noncomputable def initialValue : 𝕃 H :=
  functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff

noncomputable def finiteAlpha (x₀ : F) (N t : ℕ) : 𝕃 H :=
  ProximityPrize.SubmissionLower.FiniteHensel.liftCoeff
    (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
      (initialValue (H := H)) N t

noncomputable def Wfield : 𝕃 H :=
  liftToFunctionField (H := H) H.leadingCoeff

noncomputable def etaField (x₀ : F) (hHyp : Hypotheses x₀ R H) : 𝕃 H :=
  embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)

noncomputable def betaField (x₀ : F) (hHyp : Hypotheses x₀ R H)
    (N t : ℕ) : 𝕃 H :=
  finiteAlpha (R := R) (H := H) x₀ N t *
    (Wfield (H := H) ^ (t + 1) * etaField (R := R) (H := H) x₀ hHyp ^
      ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t)

lemma Wfield_ne_zero : Wfield (H := H) ≠ 0 := by
  exact liftToFunctionField_leadingCoeff_ne_zero (H := H)

lemma etaField_eq (x₀ : F) (hHyp : Hypotheses x₀ R H) :
    etaField (R := R) (H := H) x₀ hHyp =
      Wfield (H := H) ^ (R.natDegree - 2) * zeta R x₀ H := by
  exact embeddingOf𝒪Into𝕃_xi x₀ R H hHyp

theorem finiteAlpha_eq_betaField_div
    (x₀ : F) (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0) (N t : ℕ) :
    finiteAlpha (R := R) (H := H) x₀ N t =
      betaField (R := R) (H := H) x₀ hHyp N t /
      (Wfield (H := H) ^ (t + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t) := by
  have hW : Wfield (H := H) ≠ 0 := Wfield_ne_zero (H := H)
  have heta : etaField (R := R) (H := H) x₀ hHyp ≠ 0 := by
    rw [etaField_eq]
    exact mul_ne_zero (pow_ne_zero _ hW) hzeta
  unfold betaField
  field_simp [hW, heta]


open Finset.HasAntidiagonal in
/-- Coefficients of a finite product of ordinary polynomials. -/
theorem polynomial_coeff_prod {A : Type*} [CommSemiring A] {ι : Type*}
    [DecidableEq ι] (f : ι → A[X]) (d : ℕ) (s : Finset ι) :
    (∏ j ∈ s, f j).coeff d =
      ∑ l ∈ Finset.finsuppAntidiag s d, ∏ i ∈ s, (f i).coeff (l i) := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one,
        Polynomial.coeff_one, Finset.finsuppAntidiag_empty]
      split_ifs
      · simp only [Finset.card_singleton, Nat.cast_one]
      · simp only [Finset.card_empty, Nat.cast_zero]
  | insert a s ha ih =>
      rw [Finset.finsuppAntidiag_insert ha, Finset.prod_insert ha,
        Polynomial.coeff_mul, Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        simp only [Finset.mem_antidiagonal, Finset.sum_map, Function.Embedding.coeFn_mk,
          Finsupp.coe_update, Prod.forall]
        rintro u v rfl
        rw [ih, Finset.mul_sum, ← Finset.sum_attach]
        apply Finset.sum_congr rfl
        simp only [Finset.mem_attach, Finset.prod_insert ha, Function.update_self,
          forall_true_left, Subtype.forall]
        rintro x -
        rw [Finset.prod_congr rfl]
        intro i hi
        rw [Function.update_of_ne]
        exact ne_of_mem_of_not_mem hi ha
      · simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe,
          Finset.mem_antidiagonal, ne_eq, Finset.disjoint_left, Finset.mem_map,
          Finset.mem_attach, Function.Embedding.coeFn_mk, true_and, Subtype.exists,
          exists_prop, not_exists, not_and, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Prod.forall, Prod.mk.injEq]
        rintro u v rfl u' v' huv h k - l - hkl
        obtain rfl : u' = u := by
          simpa only [Finsupp.coe_update, Function.update_self] using DFunLike.congr_fun hkl a
        simp only [add_right_inj] at huv
        exact h rfl huv.symm

open Finset.HasAntidiagonal in
lemma polynomial_coeff_pow {A : Type*} [CommSemiring A]
    (p : A[X]) (k n : ℕ) :
    (p ^ k).coeff n =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.range k) n,
        ∏ i ∈ Finset.range k, p.coeff (l i) := by
  have h₁ (i : ℕ) : Function.const ℕ p i = p := rfl
  have h₂ (i : ℕ) : ∏ j ∈ Finset.range i, Function.const ℕ p j = p ^ i := by
    apply Finset.prod_range_induction (fun _ => p) (fun i => p ^ i) rfl i
      (fun _ => congrFun rfl)
  rw [← h₂, ← h₁ k]
  apply polynomial_coeff_prod (f := Function.const ℕ p) (d := n) (s := Finset.range k)


noncomputable def shiftedCoeffPolynomial (x₀ : F) (p : F[X][X]) : (𝕃 H)[X] :=
  ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
    (fieldTo𝕃 (H := H) x₀) (p.map (liftToFunctionField (H := H)))

lemma coeff_truncSeries_eq_if (c : ℕ → 𝕃 H) (t i : ℕ) :
    (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries c t).coeff i =
      if i ≤ t then c i else 0 := by
  by_cases hi : i ≤ t
  · rw [if_pos hi]
    exact ProximityPrize.SubmissionLower.FiniteHensel.coeff_truncSeries c t i hi
  · rw [if_neg hi]
    simp [ProximityPrize.SubmissionLower.FiniteHensel.truncSeries,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi]

lemma shiftedCoeffPolynomial_coeff_zero (x₀ : F) (p : F[X][X]) :
    (shiftedCoeffPolynomial (H := H) x₀ p).coeff 0 =
      liftToFunctionField (H := H) (p.eval (Polynomial.C x₀)) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold shiftedCoeffPolynomial
  rw [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply,
    Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero,
    Polynomial.eval_map]
  change Polynomial.eval₂ (liftToFunctionField (H := H))
    (liftToFunctionField (H := H) (Polynomial.C x₀)) p = _
  rw [Polynomial.eval₂_at_apply]


lemma ySlope_liftedR_eq_zeta (x₀ : F) :
    ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
      (initialValue (H := H)) = zeta R x₀ H := by
  simp only [ProximityPrize.SubmissionLower.FiniteHensel.ySlope, liftedR, initialValue,
    zeta, Polynomial.derivative_map, Polynomial.eval₂_map,
    Bivariate.evalX_eq_map, RationalFunctions.fieldTo𝕃, RingHom.comp_apply]
  have hh : (Polynomial.evalRingHom (liftToFunctionField (H := H) (Polynomial.C x₀))).comp
      (Polynomial.mapRingHom (liftToFunctionField (H := H))) =
      (liftToFunctionField (H := H)).comp (Polynomial.evalRingHom (Polynomial.C x₀)) := by
    ext p <;> simp [RingHom.comp_apply]
  rw [hh]


noncomputable def alphaDiagonal (x₀ : F) (N t : ℕ) : 𝕃 H :=
  (ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
    (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
      (initialValue (H := H)) N t).coeff t

noncomputable def betaDiagonal (x₀ : F) (hHyp : Hypotheses x₀ R H)
    (N t : ℕ) : 𝕃 H :=
  alphaDiagonal (R := R) (H := H) x₀ N t *
    (Wfield (H := H) ^ (t + 1) * etaField (R := R) (H := H) x₀ hHyp ^
      ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t)

lemma liftPoly_natDegree_le (x₀ : F) (N m : ℕ) :
    (ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
      (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
        (initialValue (H := H)) N m).natDegree ≤ m := by
  induction m with
  | zero => simp [ProximityPrize.SubmissionLower.FiniteHensel.liftPoly]
  | succ m ih =>
      rw [ProximityPrize.SubmissionLower.FiniteHensel.liftPoly]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact ih.trans (Nat.le_succ m)
      · calc
          _ ≤ (Polynomial.C
              (-((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
                (fun i => (ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
                  (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
                  (initialValue (H := H)) N m).coeff i) N).coeff (m + 1)) /
                ProximityPrize.SubmissionLower.FiniteHensel.ySlope
                  (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
                  (initialValue (H := H)))).natDegree +
              (Polynomial.X ^ (m + 1) : (𝕃 H)[X]).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 0 + (m + 1) := by
            gcongr <;> simp
          _ = m + 1 := by omega

lemma liftPoly_coeff_eq_diagonal (x₀ : F) (N m i : ℕ) (hi : i ≤ m) :
    (ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
      (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
        (initialValue (H := H)) N m).coeff i =
      alphaDiagonal (R := R) (H := H) x₀ N i := by
  induction m with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ m ih =>
      by_cases hitop : i = m + 1
      · subst i
        rfl
      · rw [ProximityPrize.SubmissionLower.FiniteHensel.liftPoly_succ_coeff_lt
          (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
          (initialValue (H := H)) N m i (by omega)]
        exact ih (by omega)

/-- The `𝒪`-weight is invariant under negation. -/
lemma regularWeight_neg {hH : 0 < H.natDegree} (a : 𝒪 H) (D : ℕ) :
    regularWeight hH (-a) D = regularWeight hH a D := by
  classical
  have hrep : (-a) = (Ideal.Quotient.mk (Ideal.span {monicize H})
      (-(canonicalRepOf𝒪 hH a)) : 𝒪 H) := by
    rw [map_neg, mk_canonicalRepOf𝒪]
  have hdeg : (-(canonicalRepOf𝒪 hH a)).degree < (monicize H).degree := by
    rw [Polynomial.degree_neg]; exact canonicalRepOf𝒪_degree_lt hH a
  rw [hrep, regularWeight_mk_eq_self_of_degree_lt hH hdeg, weight_neg]
  rfl

/-- `𝒪`-weight is subadditive under multiplication (bound form). -/
lemma regularWeight_mul_le' {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) {a b : 𝒪 H} {ba bb : ℕ}
    (ha : regularWeight hH a D ≤ (WithBot.some ba : WithBot ℕ))
    (hb : regularWeight hH b D ≤ (WithBot.some bb : WithBot ℕ)) :
    regularWeight hH (a * b) D ≤ (WithBot.some (ba + bb) : WithBot ℕ) := by
  classical
  have hab : a * b = (Ideal.Quotient.mk (Ideal.span {monicize H})
      (canonicalRepOf𝒪 hH a * canonicalRepOf𝒪 hH b) : 𝒪 H) := by
    rw [map_mul, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  rw [hab]
  exact (regularWeight_mk_le hD hH _).trans (weight_mul_le' ha hb)

/-- `RegularWeightLe hH a D B`: the element `a : 𝕃 H` is regular (in the image of `𝒪 H`) with a
witness whose `Λ`-weight is at most `B`. Bundles regularity together with a weight certificate so
that the Hensel-clearing expansion can be carried out with `Λ`-bookkeeping. -/
def RegularWeightLe {H : F[X][Y]} (hH : 0 < H.natDegree) (a : 𝕃 H) (D B : ℕ) : Prop :=
  ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 H b ∧
    regularWeight hH b D ≤ (WithBot.some B : WithBot ℕ)

/-- A `RegularWeightLe` certificate can always be relaxed to a larger budget. -/
lemma RegularWeightLe.mono {hH : 0 < H.natDegree} {a : 𝕃 H} {D B B' : ℕ}
    (h : RegularWeightLe hH a D B) (hBB : B ≤ B') : RegularWeightLe hH a D B' := by
  obtain ⟨b, hb, hw⟩ := h
  exact ⟨b, hb, hw.trans (by exact_mod_cast hBB)⟩

/-- Certificates multiply: budgets add.  This is the `𝕃`-side form of the sub-additivity of `Λ`
(`regularWeight_mul_le'`). -/
lemma RegularWeightLe.mul {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a b : 𝕃 H} {Ba Bb : ℕ}
    (ha : RegularWeightLe hH a D Ba) (hb : RegularWeightLe hH b D Bb) :
    RegularWeightLe hH (a * b) D (Ba + Bb) := by
  obtain ⟨a', ha', hwa⟩ := ha
  obtain ⟨b', hb', hwb⟩ := hb
  exact ⟨a' * b', by rw [ha', hb', map_mul], regularWeight_mul_le' hD hH hwa hwb⟩

/-- Certificates add at a common budget, since `Λ` of a sum is at most the max. -/
lemma RegularWeightLe.add {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a b : 𝕃 H} {B : ℕ}
    (ha : RegularWeightLe hH a D B) (hb : RegularWeightLe hH b D B) :
    RegularWeightLe hH (a + b) D B := by
  obtain ⟨a', ha', hwa⟩ := ha
  obtain ⟨b', hb', hwb⟩ := hb
  exact ⟨a' + b', by rw [ha', hb', map_add],
    (regularWeight_add_le hD hH a' b').trans (max_le hwa hwb)⟩

/-- Negation preserves a certificate, since `Λ` is invariant under negation. -/
lemma RegularWeightLe.neg {hH : 0 < H.natDegree} {a : 𝕃 H} {D B : ℕ}
    (ha : RegularWeightLe hH a D B) : RegularWeightLe hH (-a) D B := by
  obtain ⟨a', ha', hwa⟩ := ha
  exact ⟨-a', by rw [ha', map_neg], by rwa [regularWeight_neg]⟩

/-- Iterating `RegularWeightLe.mul`: a `k`-th power costs `k` times the budget. -/
lemma RegularWeightLe.pow {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a : 𝕃 H} {Ba : ℕ} (ha : RegularWeightLe hH a D Ba) (k : ℕ) :
    RegularWeightLe hH (a ^ k) D (k * Ba) := by
  induction k with
  | zero =>
      simp only [pow_zero, Nat.zero_mul]
      refine ⟨1, by rw [map_one], ?_⟩
      rw
          [show (1 : 𝒪 H) = (Ideal.Quotient.mk (Ideal.span {monicize H}) (1 : F[X][Y]) : 𝒪 H) by
              simp]
      refine (regularWeight_mk_le hD hH _).trans ?_
      rw [show (1 : F[X][Y]) = Polynomial.C 1 by simp]
      exact (weight_C_le H D 1).trans (by simp)
  | succ k ih =>
      rw [pow_succ]
      refine (RegularWeightLe.mul hD ih ha).mono ?_
      ring_nf; omega

/-- A finite sum of elements sharing a budget keeps that budget. -/
lemma RegularWeightLe.sum {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → 𝕃 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree} {B : ℕ}
    (hf : ∀ i ∈ s, RegularWeightLe hH (f i) D B) :
    RegularWeightLe hH (∑ i ∈ s, f i) D B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by rw [map_zero, Finset.sum_empty], ?_⟩
      rw [regularWeight_zero]; exact bot_le
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact RegularWeightLe.add hD (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- A finite product costs the sum of the individual budgets. -/
lemma RegularWeightLe.prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → 𝕃 H) (B : ι → ℕ)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    (hf : ∀ i ∈ s, RegularWeightLe hH (f i) D (B i)) :
    RegularWeightLe hH (∏ i ∈ s, f i) D (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      refine ⟨1, by rw [map_one], ?_⟩
      rw
          [show (1 : 𝒪 H) = (Ideal.Quotient.mk (Ideal.span {monicize H}) (1 : F[X][Y]) : 𝒪 H) by
              simp]
      refine (regularWeight_mk_le hD hH _).trans ?_
      rw [show (1 : F[X][Y]) = Polynomial.C 1 by simp]
      exact (weight_C_le H D 1).trans (by simp)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact RegularWeightLe.mul hD (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Coefficient embeddings are regular with `Λ`-weight at most their `X`-degree. -/
lemma regularWeightLe_liftToFunctionField {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree)
    (c : F[X]) : RegularWeightLe hH (liftToFunctionField (H := H) c) D c.natDegree := by
  refine ⟨(Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C c) : 𝒪 H), ?_, ?_⟩
  · rw [embeddingOf𝒪Into𝕃_mk]; rfl
  · exact (regularWeight_mk_le hD hH _).trans (weight_C_le H D c)

/-- The leading coefficient lift `W` is regular with `Λ`-weight at most `D`. -/
lemma regularWeightLe_leadingCoeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) :
    RegularWeightLe hH (liftToFunctionField (H := H) H.leadingCoeff) D D := by
  refine (regularWeightLe_liftToFunctionField hD hH H.leadingCoeff).mono ?_
  by_cases hHz : H = 0
  · simp [hHz]
  · have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHz)
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [Polynomial.leadingCoeff]; omega


/-- Sharp `Λ`-weight bound on the leading-coefficient lift `W`: `Λ(W) ≤ D - dH`.
This is the per-`W`-factor budget used in the sharp telescoping;
the looser `Λ(W) ≤ D` of `regularWeightLe_leadingCoeff` is not enough for the constant term to
telescope. -/
lemma regularWeightLe_leadingCoeff_sharp {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) :
    RegularWeightLe hH (liftToFunctionField (H := H) H.leadingCoeff) D
      (D - H.natDegree) := by
  refine (regularWeightLe_liftToFunctionField hD hH H.leadingCoeff).mono ?_
  by_cases hHz : H = 0
  · simp [hHz]
  · have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHz)
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [Polynomial.leadingCoeff]; omega

/-- The sharp per-step `Λ`-weight budget for the numerators `βₜ`:
```
sharp t = 1 + (t+1)·(D - dH) + eₜ·((dY-1)·(D - dH + 1)) + (t-1)·(D - dY)
```
with `dH = natDegreeY H`, `dY = natDegreeY R`, `eₜ = ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t`, and truncated
subtraction throughout (so the last summand vanishes for `t ≤ 1`).

## Why the last summand is there

The uncorrected bound `1 + (t+1)Λ(W) + eₜΛ(ξ)` — this one without the final `(t-1)·(D - dY)` — is
**not provable by the recursion the numerators satisfy**, for a reason easy to lose:

* In a bound-based accounting every factor of `W` that the recursion *charges* costs the bound
  `Λ(W) ≤ D - dH`, and the base case forces exactly that charge: `Λ(β₀) = Λ(T) = D - dH + 1` is
  fixed by the definition of the `Λ`-grading, so no smaller `W`-charge survives `t = 0`.
* But the recursion also *saves* one factor of `W`, via `W ∣ leadingCoeff R(x₀,·,Z)`
  (`leadingCoeff_dvd_evalX_coeff_natDegree`).  A saved `W` is only worth its **exact** degree
  `deg W`, not the bound `D - dH`; writing the coefficient as `W · c` leaves `Λ(c) = Λ(coeff) -
  deg W`, and `deg W` has no lower bound.
* Crediting the saved `W` at `Λ(W)` while using `D` as an upper bound elsewhere would amount to
  subtracting an upper bound.  Doing the accounting honestly leaves a deficit of exactly
  `Λ(c) ≤ D - dY`.

The correction `(t-1)·(D - dY)` pays for precisely that deficit, and it is *superadditive on the
only configuration where the deficit occurs*: the boundary summand needs `p.2 = t+1` split into `d`
parts each `≤ t`, hence at least two nonzero parts `S ≥ 2`, and then
`t·(D - dY) - ∑ᵢ (lᵢ-1)·(D - dY) = (S-1)·(D - dY) ≥ D - dY`.
Every other summand satisfies `∑ᵢ (lᵢ-1) ≤ t`, so the correction never costs anything there.

## Why the correction costs nothing

`numeratorShapeSharp_le_loose` still gives the loose bound `(2t+1)·dY·D`, and that is the form
consumers want, since the correction is invisible to the telescoping they perform:
`max_t (sharp t + (k-t)Λ(W) + (e_k-eₜ)Λ(ξ)) = sharp k ≤ (2k+1)·dY·D`.

The uncorrected bound would follow instead from `Λ(αₜ) ≤ Λ(T) - Λ(W)`, i.e. from a weight function
on `𝕃` rather than on `𝒪`, giving `Λ(T) + t·deg W ≤ 1 + (t+1)(D - dH)`.  That route is not taken
here: bounding the quotient `αₜ = -cₜ/ζ` needs a *lower* bound on `Λ(ζ)`, and only upper bounds are
available. -/
def numeratorShapeSharp (R : F[X][X][Y]) (H : F[X][Y]) (D t : ℕ) : ℕ :=
  1 + (t + 1) * (D - Bivariate.natDegreeY H) +
    ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t *
      ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) +
    (t - 1) * (D - Bivariate.natDegreeY R)

/-- The sharp bound weakens to the loose paper bound consumed by the final assembly:
`sharp t ≤ (2t+1)·dY·D`.  Pure arithmetic, using `dH ≥ 1`, `dH ≤ dY`, `dH ≤ D`, and
`eₜ ≤ 2t`. -/
lemma numeratorShapeSharp_le_loose (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D) (t : ℕ) :
    numeratorShapeSharp R H D t ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := by
  -- Translate the degree facts into the bare numeric hypotheses needed by the arithmetic.
  have hdH_dY : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hdH_pos : 1 ≤ Bivariate.natDegreeY H := hH
  have hdH_D : Bivariate.natDegreeY H ≤ D := by
    have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (by rintro rfl; simp at hH))
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [show Bivariate.natDegreeY H = H.natDegree from rfl]; omega
  have het : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t ≤ 2 * t := by
    simp [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent]
  unfold numeratorShapeSharp
  set D' := D
  set dH := Bivariate.natDegreeY H with hdHdef
  set dY := Bivariate.natDegreeY R with hdYdef
  set et := ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent t with hetdef
  clear_value D' dH dY et
  obtain ⟨a, rfl⟩ : ∃ a, D' = dH + a := ⟨D' - dH, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, dY = dH + b := ⟨dY - dH, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, dH = c + 1 := ⟨dH - 1, by omega⟩
  simp only [Nat.add_sub_cancel_left] at *
  rw [show c + 1 + b - 1 = c + b by omega, show c + 1 + a - (c + 1 + b) = a - b by omega]
  -- `P` is the `ξ`-charge; the correction contributes at most `t * a`
  set P := (c + b) * (a + 1) with hPdef
  have hA : et * P ≤ 2 * t * P := Nat.mul_le_mul_right _ (by omega)
  have hCorr : (t - 1) * (a - b) ≤ t * a := Nat.mul_le_mul (by omega) (by omega)
  -- the right-hand side dominates `(2t+1)·(P + a + 1)`
  have hRHSexp : P + a + 1 + ((c + b) * c + c) = (c + 1 + b) * (c + 1 + a) := by
    rw [hPdef]; ring
  have hRHS : (2 * t + 1) * (P + a + 1) ≤ (2 * t + 1) * ((c + 1 + b) * (c + 1 + a)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hPle : 2 * t * P ≤ (2 * t + 1) * P := Nat.mul_le_mul_right _ (by omega)
  calc 1 + (t + 1) * a + et * P + (t - 1) * (a - b)
      ≤ 1 + (t + 1) * a + 2 * t * P + t * a :=
        Nat.add_le_add (Nat.add_le_add_left hA _) hCorr
    _ = 1 + (2 * t + 1) * a + 2 * t * P := by ring
    _ ≤ (2 * t + 1) * P + (2 * t + 1) * a + (2 * t + 1) := by omega
    _ = (2 * t + 1) * (P + a + 1) := by ring
    _ ≤ (2 * t + 1) * ((c + 1 + b) * (c + 1 + a)) := hRHS
    _ = (2 * t + 1) * (c + 1 + b) * (c + 1 + a) := by ring

/-- `RegularWeightLe`-version of the bridge from the embedded `𝒪`-witness back to the `𝒪`-weight:
if `embeddingOf𝒪Into𝕃 H b` is regular with `Λ`-witness of weight `≤ B`, then so is the canonical
witness `b` itself (by injectivity of the embedding). -/
lemma regularWeight_le_of_regularWeightLe {hH : 0 < H.natDegree} {D B : ℕ} (b : 𝒪 H)
    (h : RegularWeightLe hH (embeddingOf𝒪Into𝕃 H b) D B) :
    regularWeight hH b D ≤ (WithBot.some B : WithBot ℕ) := by
  obtain ⟨b', heq, hw⟩ := h
  rwa [embeddingOf𝒪Into𝕃_injective hH heq]



lemma regularWeightLe_polyX_coeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (n : ℕ) :
    RegularWeightLe hH ((Polynomial.X : (𝕃 H)[X]).coeff n) D 0 := by
  rw [Polynomial.coeff_X]
  split
  · rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) 1 by simp]
    exact (regularWeightLe_liftToFunctionField hD hH 1).mono (by simp)
  · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
    exact (regularWeightLe_liftToFunctionField hD hH 0).mono (by simp)

lemma regularWeightLe_polyC_coeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (x₀ : F) (n : ℕ) :
    RegularWeightLe hH ((Polynomial.C (fieldTo𝕃 (H := H) x₀) : (𝕃 H)[X]).coeff n) D 0 := by
  rw [Polynomial.coeff_C]
  split
  · change RegularWeightLe hH (liftToFunctionField (H := H) (Polynomial.C x₀)) D 0
    exact (regularWeightLe_liftToFunctionField hD hH _).mono (by simp)
  · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
    exact (regularWeightLe_liftToFunctionField hD hH 0).mono (by simp)

lemma regularWeightLe_binomial_coeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (x₀ : F) (s : ℕ) : ∀ n,
    RegularWeightLe hH
      (((Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X : (𝕃 H)[X]) ^ s).coeff n) D 0 := by
  induction s with
  | zero =>
      intro n
      simp only [pow_zero]
      rw [Polynomial.coeff_one]
      split
      · rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) 1 by simp]
        exact (regularWeightLe_liftToFunctionField hD hH 1).mono (by simp)
      · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
        exact (regularWeightLe_liftToFunctionField hD hH 0).mono (by simp)
  | succ s ih =>
      intro n
      rw [pow_succ, Polynomial.coeff_mul]
      refine RegularWeightLe.sum _ _ hD ?_
      intro pr hpr
      have h2 : RegularWeightLe hH
          ((Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X : (𝕃 H)[X]).coeff pr.2) D 0 := by
        rw [Polynomial.coeff_add]
        exact RegularWeightLe.add hD
          (regularWeightLe_polyC_coeff hD hH x₀ pr.2)
          (regularWeightLe_polyX_coeff hD hH pr.2)
      exact (RegularWeightLe.mul hD (ih pr.1) h2).mono (by simp)

lemma regularWeightLe_shiftedCoeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (x₀ : F) (p : F[X][X]) (n : ℕ) :
    RegularWeightLe hH ((shiftedCoeffPolynomial (H := H) x₀ p).coeff n) D
      (Bivariate.totalDegree p) := by
  classical
  unfold shiftedCoeffPolynomial
  rw [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply]
  change RegularWeightLe hH
    ((Polynomial.eval₂ (Polynomial.C : 𝕃 H →+* (𝕃 H)[X])
      (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X)
      (p.map (liftToFunctionField (H := H)))).coeff n) D _
  rw [Polynomial.eval₂_eq_sum_range]
  have hcoeff :
      (∑ i ∈ Finset.range ((p.map (liftToFunctionField (H := H))).natDegree + 1),
        Polynomial.C ((p.map (liftToFunctionField (H := H))).coeff i) *
          (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X) ^ i).coeff n =
      ∑ i ∈ Finset.range ((p.map (liftToFunctionField (H := H))).natDegree + 1),
        (Polynomial.C ((p.map (liftToFunctionField (H := H))).coeff i) *
          (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X) ^ i).coeff n := by simp
  rw [hcoeff]
  refine RegularWeightLe.sum _ _ hD ?_
  intro i hi
  rw [Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_map]
  refine (RegularWeightLe.mul hD
    (regularWeightLe_liftToFunctionField hD hH (p.coeff i))
    (regularWeightLe_binomial_coeff hD hH x₀ i n)).mono ?_
  rw [Nat.add_zero]
  rcases Bivariate.coeff_totalDegree_le' p i with h | h0
  · omega
  · rw [h0]; simp


lemma regularWeightLe_shiftedCoeff_yz {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (x₀ : F) (p : F[X][X]) {B : ℕ}
    (hp : ∀ a, p.coeff a ≠ 0 → (p.coeff a).natDegree ≤ B) (n : ℕ) :
    RegularWeightLe hH ((shiftedCoeffPolynomial (H := H) x₀ p).coeff n) D
      B := by
  classical
  unfold shiftedCoeffPolynomial
  rw [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply]
  change RegularWeightLe hH
    ((Polynomial.eval₂ (Polynomial.C : 𝕃 H →+* (𝕃 H)[X])
      (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X)
      (p.map (liftToFunctionField (H := H)))).coeff n) D _
  rw [Polynomial.eval₂_eq_sum_range]
  have hcoeff :
      (∑ i ∈ Finset.range ((p.map (liftToFunctionField (H := H))).natDegree + 1),
        Polynomial.C ((p.map (liftToFunctionField (H := H))).coeff i) *
          (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X) ^ i).coeff n =
      ∑ i ∈ Finset.range ((p.map (liftToFunctionField (H := H))).natDegree + 1),
        (Polynomial.C ((p.map (liftToFunctionField (H := H))).coeff i) *
          (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X) ^ i).coeff n := by simp
  rw [hcoeff]
  refine RegularWeightLe.sum _ _ hD ?_
  intro i hi
  rw [Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_map]
  refine (RegularWeightLe.mul hD
    (regularWeightLe_liftToFunctionField hD hH (p.coeff i))
    (regularWeightLe_binomial_coeff hD hH x₀ i n)).mono ?_
  rw [Nat.add_zero]
  by_cases hpi : p.coeff i = 0
  · rw [hpi]; simp
  · exact hp i hpi

set_option maxHeartbeats 2000000 in
-- The `Finset.finsuppAntidiag` case split below expands one a finite polynomial coefficient of a
-- `d`-fold product into a sum over compositions, and each summand carries a `RegularWeightLe`
-- certificate assembled from seven `.mul`/`.pow`/`.sum` steps; the default heartbeat budget is
-- exhausted by the resulting `ring`/`omega` normalisations.
/-- Weight-tracking per-degree clearing lemma: the `Λ`-graded analogue of
`finiteHenselClearedTerm_regular`.  Each degree-`j` summand of the cleared `(t+1)`-st residual is
regular with sharp `Λ`-weight at most `numeratorShapeSharp R H D (t+1)`.

The proof splits on the *boundary* summand `p.1 = 0`, `j = d ≥ 2`, `p.2 = t+1`, which is the one
place where the `d` part-certificates want one more factor of `W` than the goal supplies.  There the
leading-coefficient divisibility `W ∣ leadingCoeff R(x₀,·,Z)` frees that factor, at the cost of a
`Λ(c) ≤ D - dY` coefficient charge, and the correction term of `numeratorShapeSharp` pays for it —
see that definition's docstring for why the correction is needed and why the paper's uncorrected
form is not provable on this route. -/
lemma finiteHenselClearedTerm_weight (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (t : ℕ) (αtrunc : ℕ → 𝕃 H)
    (ihNum : ∀ i, i ≤ t →
      RegularWeightLe hH
        (αtrunc i * (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i))
        D (numeratorShapeSharp R H D i))
    (hαzero : ∀ i, t < i → αtrunc i = 0)
    (j : ℕ) (hj : j ∈ Finset.range (R.natDegree + 1)) :
    RegularWeightLe hH
      ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) * (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t) ^ j).coeff (t + 1) *
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
          liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)))
      D (numeratorShapeSharp R H D (t + 1)) := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) with hetadef
  -- abbreviations for the sharp weight atoms
  set ΛW : ℕ := D - Bivariate.natDegreeY H with hΛWdef
  set Λξ : ℕ := (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) with hΛξdef
  -- base RegularWeightLe certificates for W and ξ at the SHARP weights
  have hRWLW : RegularWeightLe hH W D ΛW := by
    rw [hWdef, hΛWdef]
    exact regularWeightLe_leadingCoeff_sharp hD_H hH
  have hRWLeta : RegularWeightLe hH eta D Λξ := by
    rw [hetadef, hΛξdef]
    -- ξ as an 𝒪-element
    obtain ⟨b, hb⟩ : ∃ b : 𝒪 H, embeddingOf𝒪Into𝕃 H b = eta := ⟨xi x₀ R H hHyp, rfl⟩
    refine ⟨xi x₀ R H hHyp, rfl, ?_⟩
    exact xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hjle : j ≤ R.natDegree := by rw [Finset.mem_range] at hj; omega
  have hdH_le_R : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hdY : Bivariate.natDegreeY R = R.natDegree := rfl
  have hdH : Bivariate.natDegreeY H = H.natDegree := rfl
  -- distribute coeff_mul and coeff_pow into a sum over (p, l)
  rw [Polynomial.coeff_mul, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro p _hp
  rw [polynomial_coeff_pow]
  simp only [coeff_truncSeries_eq_if]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp _hp
  -- Case A: some part exceeds t ⇒ a zero factor ⇒ weight 0.
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j,
        if l i ≤ t then αtrunc (l i) else 0) = 0 := by
      apply Finset.prod_eq_zero hi₀
      rw [if_neg (by omega)]
    rw [hz]
    refine ⟨0, by simp, ?_⟩
    rw [regularWeight_zero]; exact bot_le
  · -- Case B: all parts ≤ t.
    push Not at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    have hprod_if : (∏ i ∈ Finset.range j,
        if l i ≤ t then αtrunc (l i) else 0) =
        ∏ i ∈ Finset.range j, αtrunc (l i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_pos (hle i hi)]
    rw [hprod_if]
    -- product-clearing weight: ∏ αtrunc(l i) · W^Pw · eta^Pe  has weight ≤ ∑ sharp(l i)
    set Pw : ℕ := (∑ i ∈ Finset.range j, (l i + 1)) with hPwdef
    set Pe : ℕ := (∑ i ∈ Finset.range j, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) with hPedef
    set E1 : ℕ := ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1 with hE1def
    have hPweq : Pw = p.2 + j := by rw [hPwdef, Finset.sum_add_distrib, hbsum]; simp
    have hprodW : RegularWeightLe hH
        ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) D
        (∑ i ∈ Finset.range j, numeratorShapeSharp R H D (l i)) := by
      rw [hPwdef, hPedef, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine RegularWeightLe.prod _ _ _ hD_H ?_
      intro i hi
      have := ihNum (l i) (hle i hi)
      -- rearrange W^(l i+1)*eta^e to match
      have hrw : αtrunc (l i) * (W ^ (l i + 1) * eta ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) =
          αtrunc (l i) * (W ^ (l i + 1) * eta ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) := rfl
      rw [hWdef, hetadef] at this ⊢
      exact this
    -- `S1` counts the nonzero parts; `Pc` is the correction budget the parts consume
    set S1 : ℕ := (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) with hS1def
    set Pc : ℕ := (∑ i ∈ Finset.range j, (l i - 1)) with hPcdef
    set G : ℕ := D - Bivariate.natDegreeY R with hGdef
    have h2b : 2 * p.2 = Pe + S1 := by
      rw [hPedef, hS1def, ← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        unfold ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent; split <;> omega
    have hbS1 : p.2 ≤ t * S1 := by
      rw [← hbsum, hS1def, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      split
      · next h => rw [h]; simp
      · next h => rw [Nat.mul_one]; exact hle i hi
    -- each part spends `lᵢ - 1` of the correction and `1` of the nonzero count, out of `lᵢ`
    have hPcS1 : Pc + S1 ≤ p.2 := by
      rw [hPcdef, hS1def, ← hbsum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      split
      · next h => omega
      · next h => omega
    -- no nonzero parts means no correction is consumed at all
    have hS1zero : S1 = 0 → Pc = 0 := by
      intro h0
      have hsum0 : (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) = 0 := by
        rw [← hS1def]; exact h0
      rw [hPcdef]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi0 := Finset.sum_eq_zero_iff.mp hsum0 i hi
      by_cases hli : l i = 0
      · omega
      · rw [if_neg hli] at hi0; omega
    -- so the parts never consume more correction than the `t` available at `t+1`
    have hPc_le : Pc ≤ t := by
      rcases Nat.eq_zero_or_pos S1 with hS0 | hS1pos
      · have := hS1zero hS0; omega
      · omega
    -- the eta exponent bound Pe ≤ E1 = 2t
    have hPe_le : Pe ≤ E1 := by
      have hE1' : E1 = 2 * t := by
        rw [hE1def, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      rw [hE1']
      rcases Nat.lt_or_ge p.2 (t + 1) with hbt | hbt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h; push Not at h; interval_cases S1 <;> omega
        omega
    -- sharp-sum identity: ∑ sharp(l i) = j + Pw*ΛW + Pe*Λξ + Pc*G
    have hsharpSum : (∑ i ∈ Finset.range j, numeratorShapeSharp R H D (l i)) =
        j + Pw * ΛW + Pe * Λξ + Pc * G := by
      have hexpand : ∀ i, numeratorShapeSharp R H D (l i) =
          1 + (l i + 1) * ΛW + ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i) * Λξ + (l i - 1) * G := by
        intro i; rw [numeratorShapeSharp, hΛWdef, hΛξdef, hGdef]
      simp only [hexpand]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hPwdef, ← hPedef, ← hPcdef]
    -- W exponent budget (NON-boundary): wb = (t+2)+(d-2).
    -- E1 leftover: eta^(E1 - Pe).
    -- coefficient weight ≤ totalDegree (R.coeff j) ≤ D - j
    have hcoeffW : RegularWeightLe hH
        ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1) D
        (Bivariate.totalDegree (R.coeff j)) := regularWeightLe_shiftedCoeff hD_H hH x₀ (R.coeff j) p.1
    have htd_le : Bivariate.totalDegree (R.coeff j) ≤ D - j := by
      by_cases hjs : j ∈ R.support
      · have := hD_R j hjs; omega
      · have hz : R.coeff j = 0 := by
          by_contra hne; exact hjs (Polynomial.mem_support_iff.mpr hne)
        rw [hz]; simp [Bivariate.totalDegree]
    -- key arithmetic facts
    have hkey : D ≤ R.natDegree + ΛW := by
      rw [hΛWdef]
      have : Bivariate.natDegreeY H ≤ R.natDegree := by rw [← hdY]; exact hdH_le_R
      rw [hdH] at this
      omega
    have hjd : j ≤ R.natDegree := hjle
    have hdD : R.natDegree ≤ D := by
      by_cases hRz : R = 0
      · simp [hRz]
      · have hmem : R.natDegree ∈ R.support :=
          Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hRz)
        have := hD_R R.natDegree hmem; omega
    have hjD : j ≤ D := le_trans hjd hdD
    -- boundary detection
    by_cases hbdry : p.2 = t + 1 ∧ j = R.natDegree ∧ 2 ≤ R.natDegree
    · -- BOUNDARY CASE: `p.1 = 0`, `j = d = R.natDegree ≥ 2`, `p.2 = t+1`.
      --
      -- The `d` part-certificates consume `Pw = p.2 + j = t+d+1` factors of `W`, one more than the
      -- `wb = (t+2) + (d-2) = t+d` the goal supplies.  The missing factor comes from the
      -- leading-coefficient divisibility `W ∣ leadingCoeff R(x₀,·,Z)`
      -- (`leadingCoeff_dvd_evalX_coeff_natDegree`): writing that coefficient as `W * c` turns the
      -- coefficient charge from `D - d` into `Λ(c) = c.natDegree ≤ D - d`, and frees the `W`.
      --
      -- The resulting deficit is exactly `c.natDegree`, and it is paid by the correction term of
      -- `numeratorShapeSharp`: this branch forces `p.2 = t+1` split into parts each `≤ t`, hence at
      -- least two nonzero parts, so the parts consume at most `Pc ≤ t-1` of the correction while
      -- the target provides `t`, leaving `(S₁-1)·G ≥ G = D - dY ≥ c.natDegree`.  See the
      -- docstring of `numeratorShapeSharp` for why the paper's uncorrected form is not provable
      -- here.
      obtain ⟨hb2, hjd', hd2⟩ := hbdry
      have hp1 : p.1 = 0 := by omega
      -- at least two nonzero parts, since each part is `≤ t` but they sum to `t+1`
      have hS1ge : 2 ≤ S1 := by
        by_contra h
        push Not at h
        interval_cases S1 <;> omega
      have hPc_lt : Pc + 1 ≤ t := by omega
      -- the boundary coefficient is `W * c`
      have hdvd : H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree :=
        leadingCoeff_dvd_evalX_coeff_natDegree hHyp
      obtain ⟨c, hc⟩ := hdvd
      have hcoeff_eq : (R.coeff R.natDegree).eval (Polynomial.C x₀) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
        simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
      have hW_ne : H.leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hH)
      -- `c.natDegree ≤ G = D - dY`, since `W * c` is a coefficient of `R(x₀,·,Z)`
      have hc_deg : c.natDegree ≤ G := by
        rw [hGdef]
        by_cases hc0 : c = 0
        · rw [hc0]; simp
        · have hne : (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree ≠ 0 := by
            rw [hc]; exact mul_ne_zero hW_ne hc0
          have hle' : c.natDegree ≤
              ((Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree).natDegree := by
            refine Polynomial.natDegree_le_of_dvd ?_ hne
            exact hc ▸ Dvd.intro_left _ rfl
          have hbound : ((Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree).natDegree ≤
              D - R.natDegree :=
            natDegree_coeff_le_of_totalDegree_le _ hD_Rx0 R.natDegree
          rw [hdY]; omega
      -- rewrite the coefficient factor as `W * lift c`
      have hcoeff_split :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 =
            W * liftToFunctionField (H := H) c := by
        rw [hp1, hjd', shiftedCoeffPolynomial_coeff_zero, hcoeff_eq, hc, map_mul, hWdef]
      -- the freed `W` completes `W^Pw`, so the parts certificate applies verbatim
      have hPweq' : Pw = t + 1 + R.natDegree := by rw [hPweq, hb2, hjd']
      have hreassoc :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          liftToFunctionField (H := H) c *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            eta ^ (E1 - Pe) := by
        rw [hcoeff_split, hPweq']
        have hWpow : W * (W ^ (t + 1 + 1) * W ^ (R.natDegree - 2)) = W ^ (t + 1 + R.natDegree) := by
          rw [← pow_add, ← pow_succ']
          congr 1
          omega
        have hEpow : eta ^ E1 = eta ^ Pe * eta ^ (E1 - Pe) := by
          rw [← pow_add]
          congr 1
          omega
        calc W * liftToFunctionField (H := H) c *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2))
            = liftToFunctionField (H := H) c * (∏ i ∈ Finset.range j, αtrunc (l i)) *
                ((W * (W ^ (t + 1 + 1) * W ^ (R.natDegree - 2))) * eta ^ E1) := by ring
          _ = liftToFunctionField (H := H) c * (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + R.natDegree) * (eta ^ Pe * eta ^ (E1 - Pe))) := by
                rw [hWpow, hEpow]
          _ = liftToFunctionField (H := H) c *
                ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                  (W ^ (t + 1 + R.natDegree) * eta ^ Pe)) * eta ^ (E1 - Pe) := by ring
      rw [hreassoc]
      refine (RegularWeightLe.mul hD_H
        (RegularWeightLe.mul hD_H
          ((regularWeightLe_liftToFunctionField hD_H hH c).mono hc_deg) hprodW)
        (hRWLeta.pow hD_H _)).mono ?_
      rw [hsharpSum]
      have hsharpSucc : numeratorShapeSharp R H D (t + 1) =
          1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by
        rw [numeratorShapeSharp, ← hΛWdef, ← hΛξdef, ← hGdef, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
        rw [show t + 1 + 1 = t + 2 by omega,
          show t + 1 - 1 = t by omega]
      rw [hsharpSucc]
      -- `Λξ = (dY-1)·(ΛW+1)` and `G = D - dY`, so the whole thing is linear arithmetic
      have hΛξval : Λξ = (R.natDegree - 1) * (ΛW + 1) := by rw [hΛξdef, hΛWdef, hdY]
      have hGval : G = D - R.natDegree := by rw [hGdef, hdY]
      have hE1val : E1 = 2 * t := by rw [hE1def, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      -- expand the two products so that only `ΛW`-linear atoms remain
      obtain ⟨dm, hdmeq⟩ : ∃ dm, R.natDegree = dm + 2 := ⟨R.natDegree - 2, by omega⟩
      have hΛξexp : Λξ = dm * ΛW + dm + ΛW + 1 := by
        rw [hΛξval, hdmeq, show dm + 2 - 1 = dm + 1 by omega]; ring
      have hPwexp : Pw * ΛW = (t + 1) * ΛW + dm * ΛW + 2 * ΛW := by
        rw [hPweq', hdmeq]; ring
      have hPeval : Pe * Λξ + (E1 - Pe) * Λξ = 2 * t * Λξ := by
        rw [← Nat.add_mul, hE1val]; congr 1; omega
      have hPcG : G + Pc * G ≤ t * G := by
        calc G + Pc * G = (Pc + 1) * G := by ring
          _ ≤ t * G := Nat.mul_le_mul_right _ hPc_lt
      -- everything but `G + Pc·G ≤ t·G` is a ring identity: the `W`- and `ξ`-charges match exactly
      calc G + (j + Pw * ΛW + Pe * Λξ + Pc * G) + (E1 - Pe) * Λξ
          = (j + Pw * ΛW + (Pe * Λξ + (E1 - Pe) * Λξ)) + (G + Pc * G) := by ring
        _ = (j + Pw * ΛW + E1 * Λξ) + (G + Pc * G) := by
              rw [← Nat.add_mul, Nat.add_sub_cancel' hPe_le]
        _ ≤ (j + Pw * ΛW + E1 * Λξ) + t * G := Nat.add_le_add_left hPcG _
        _ = 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by
              rw [hjd', hPweq', hE1val, hΛξexp, hdmeq]; ring
    · -- NON-BOUNDARY: budget Pw ≤ (t+2)+(d-2) covers everything.
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) := by
        rw [hPweq, Finset.mem_range] at *
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · omega
        · rcases not_and_or.mp hbdry with h1 | h2
          · omega
          · rcases not_and_or.mp h2 with h3 | h4
            · omega
            · exact absurd hd h4
      -- reassociate to isolate W^(wb-Pw) and eta^(E1-Pe)
      have hreassoc :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2)) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2)) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2)) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ ((t + 1 + 1) + (R.natDegree - 2)) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      refine (RegularWeightLe.mul hD_H
        (RegularWeightLe.mul hD_H (hcoeffW.mono htd_le) hprodW)
        (RegularWeightLe.mul hD_H (hRWLW.pow hD_H _) (hRWLeta.pow hD_H _))).mono ?_
      -- weight: (D-j) + (j + Pw*ΛW + Pe*Λξ) + ((wb-Pw)*ΛW + (E1-Pe)*Λξ) ≤ sharp(t+1)
      rw [hsharpSum]
      -- sharp(t+1) expansion
      have hsharpSucc : numeratorShapeSharp R H D (t + 1) =
          1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by
        rw [numeratorShapeSharp, ← hΛWdef, ← hΛξdef, ← hGdef, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
        rw [show t + 1 + 1 = t + 2 by omega,
          show t + 1 - 1 = t by omega]
      rw [hsharpSucc]
      -- now pure arithmetic (verified separately)
      set wb := (t + 1 + 1) + (R.natDegree - 2) with hwbdef
      have hE1val : E1 = 2 * t := by rw [hE1def, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      have hwb_le : wb ≤ t + R.natDegree := by
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · -- d < 2: then not boundary forces nothing, but budget? wb = (t+2)+0 = t+2
          rw [hwbdef]; omega
        · rw [hwbdef]; omega
      -- reduce via cancellations
      have hAcancel : Pw * ΛW + (wb - Pw) * ΛW = wb * ΛW := by
        rw [← Nat.add_mul]; congr 1; omega
      have hBcancel : Pe * Λξ + (E1 - Pe) * Λξ = E1 * Λξ := by
        rw [← Nat.add_mul]; congr 1; omega
      have hjDj : D - j + j = D := Nat.sub_add_cancel hjD
      -- Final: (D-j) + (j + Pw ΛW + Pe Λξ) + ((wb-Pw)ΛW + (E1-Pe)Λξ) = D + wb*ΛW + E1*Λξ
      have hΛξval : Λξ = (R.natDegree - 1) * (ΛW + 1) := by
        rw [hΛξdef, hΛWdef, hdY]
      -- prove ≤
      have hfin0 : (D - j) + (j + Pw * ΛW + Pe * Λξ) +
          ((wb - Pw) * ΛW + (E1 - Pe) * Λξ) ≤ 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ := by
        have e1 : (D - j) + (j + Pw * ΛW + Pe * Λξ) + ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)
            = D + wb * ΛW + E1 * Λξ := by
          rw [← hjDj] at *
          -- use cancellations
          have := hAcancel; have := hBcancel
          omega
        rw [e1, hE1val, hΛξval]
        -- D + wb*ΛW + 2t*((d-1)(ΛW+1)) ≤ 1 + (t+2)ΛW + (2t+1)((d-1)(ΛW+1))
        obtain ⟨gap, hgap⟩ : ∃ g, t + R.natDegree = wb + g := ⟨t + R.natDegree - wb, by omega⟩
        obtain ⟨dm, hdmeq⟩ : ∃ dm, R.natDegree = dm + 1 := ⟨R.natDegree - 1, by
          rcases Nat.lt_or_ge R.natDegree 2 with h | h
          · -- d < 2 ⇒ d ≤ 1; need d ≥ 1: R.natDegree ≥ natDegreeY H ≥ 1
            have : 1 ≤ R.natDegree := by rw [← hdY]; rw [← hdH] at *; omega
            omega
          · omega⟩
        rw [hdmeq] at hkey ⊢
        rw [show dm + 1 - 1 = dm by omega]
        nlinarith [hkey, hwb_le, hgap, Nat.mul_le_mul_right ΛW hwb_le]
      -- the correction the parts consume is at most the `t·G` the target provides
      calc (D - j) + (j + Pw * ΛW + Pe * Λξ + Pc * G) +
            ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)
          = ((D - j) + (j + Pw * ΛW + Pe * Λξ) + ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)) + Pc * G := by
            ring
        _ ≤ (1 + (t + 2) * ΛW + (2 * t + 1) * Λξ) + t * G :=
            Nat.add_le_add hfin0 (Nat.mul_le_mul_right _ hPc_le)
        _ = 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by ring




set_option maxHeartbeats 2000000 in
lemma finiteHenselClearedTerm_weight_yz (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (t : ℕ) (αtrunc : ℕ → 𝕃 H)
    (ihNum : ∀ i, i ≤ t →
      RegularWeightLe hH
        (αtrunc i * (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i))
        D (numeratorShapeSharp R H D i))
    (hαzero : ∀ i, t < i → αtrunc i = 0)
    (j : ℕ) (hj : j ∈ Finset.range (R.natDegree + 1)) :
    RegularWeightLe hH
      ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) * (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t) ^ j).coeff (t + 1) *
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
          liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)))
      D (numeratorShapeSharp R H D (t + 1)) := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) with hetadef
  -- abbreviations for the sharp weight atoms
  set ΛW : ℕ := D - Bivariate.natDegreeY H with hΛWdef
  set Λξ : ℕ := (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) with hΛξdef
  -- base RegularWeightLe certificates for W and ξ at the SHARP weights
  have hRWLW : RegularWeightLe hH W D ΛW := by
    rw [hWdef, hΛWdef]
    exact regularWeightLe_leadingCoeff_sharp hD_H hH
  have hRWLeta : RegularWeightLe hH eta D Λξ := by
    rw [hetadef, hΛξdef]
    -- ξ as an 𝒪-element
    obtain ⟨b, hb⟩ : ∃ b : 𝒪 H, embeddingOf𝒪Into𝕃 H b = eta := ⟨xi x₀ R H hHyp, rfl⟩
    refine ⟨xi x₀ R H hHyp, rfl, ?_⟩
    exact xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hjle : j ≤ R.natDegree := by rw [Finset.mem_range] at hj; omega
  have hdH_le_R : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hdY : Bivariate.natDegreeY R = R.natDegree := rfl
  have hdH : Bivariate.natDegreeY H = H.natDegree := rfl
  -- distribute coeff_mul and coeff_pow into a sum over (p, l)
  rw [Polynomial.coeff_mul, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro p _hp
  rw [polynomial_coeff_pow]
  simp only [coeff_truncSeries_eq_if]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp _hp
  -- Case A: some part exceeds t ⇒ a zero factor ⇒ weight 0.
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j,
        if l i ≤ t then αtrunc (l i) else 0) = 0 := by
      apply Finset.prod_eq_zero hi₀
      rw [if_neg (by omega)]
    rw [hz]
    refine ⟨0, by simp, ?_⟩
    rw [regularWeight_zero]; exact bot_le
  · -- Case B: all parts ≤ t.
    push Not at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    have hprod_if : (∏ i ∈ Finset.range j,
        if l i ≤ t then αtrunc (l i) else 0) =
        ∏ i ∈ Finset.range j, αtrunc (l i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_pos (hle i hi)]
    rw [hprod_if]
    -- product-clearing weight: ∏ αtrunc(l i) · W^Pw · eta^Pe  has weight ≤ ∑ sharp(l i)
    set Pw : ℕ := (∑ i ∈ Finset.range j, (l i + 1)) with hPwdef
    set Pe : ℕ := (∑ i ∈ Finset.range j, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) with hPedef
    set E1 : ℕ := ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1 with hE1def
    have hPweq : Pw = p.2 + j := by rw [hPwdef, Finset.sum_add_distrib, hbsum]; simp
    have hprodW : RegularWeightLe hH
        ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) D
        (∑ i ∈ Finset.range j, numeratorShapeSharp R H D (l i)) := by
      rw [hPwdef, hPedef, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine RegularWeightLe.prod _ _ _ hD_H ?_
      intro i hi
      have := ihNum (l i) (hle i hi)
      -- rearrange W^(l i+1)*eta^e to match
      have hrw : αtrunc (l i) * (W ^ (l i + 1) * eta ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) =
          αtrunc (l i) * (W ^ (l i + 1) * eta ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) := rfl
      rw [hWdef, hetadef] at this ⊢
      exact this
    -- `S1` counts the nonzero parts; `Pc` is the correction budget the parts consume
    set S1 : ℕ := (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) with hS1def
    set Pc : ℕ := (∑ i ∈ Finset.range j, (l i - 1)) with hPcdef
    set G : ℕ := D - Bivariate.natDegreeY R with hGdef
    have h2b : 2 * p.2 = Pe + S1 := by
      rw [hPedef, hS1def, ← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        unfold ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent; split <;> omega
    have hbS1 : p.2 ≤ t * S1 := by
      rw [← hbsum, hS1def, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      split
      · next h => rw [h]; simp
      · next h => rw [Nat.mul_one]; exact hle i hi
    -- each part spends `lᵢ - 1` of the correction and `1` of the nonzero count, out of `lᵢ`
    have hPcS1 : Pc + S1 ≤ p.2 := by
      rw [hPcdef, hS1def, ← hbsum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      split
      · next h => omega
      · next h => omega
    -- no nonzero parts means no correction is consumed at all
    have hS1zero : S1 = 0 → Pc = 0 := by
      intro h0
      have hsum0 : (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) = 0 := by
        rw [← hS1def]; exact h0
      rw [hPcdef]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi0 := Finset.sum_eq_zero_iff.mp hsum0 i hi
      by_cases hli : l i = 0
      · omega
      · rw [if_neg hli] at hi0; omega
    -- so the parts never consume more correction than the `t` available at `t+1`
    have hPc_le : Pc ≤ t := by
      rcases Nat.eq_zero_or_pos S1 with hS0 | hS1pos
      · have := hS1zero hS0; omega
      · omega
    -- the eta exponent bound Pe ≤ E1 = 2t
    have hPe_le : Pe ≤ E1 := by
      have hE1' : E1 = 2 * t := by
        rw [hE1def, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      rw [hE1']
      rcases Nat.lt_or_ge p.2 (t + 1) with hbt | hbt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h; push Not at h; interval_cases S1 <;> omega
        omega
    -- sharp-sum identity: ∑ sharp(l i) = j + Pw*ΛW + Pe*Λξ + Pc*G
    have hsharpSum : (∑ i ∈ Finset.range j, numeratorShapeSharp R H D (l i)) =
        j + Pw * ΛW + Pe * Λξ + Pc * G := by
      have hexpand : ∀ i, numeratorShapeSharp R H D (l i) =
          1 + (l i + 1) * ΛW + ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i) * Λξ + (l i - 1) * G := by
        intro i; rw [numeratorShapeSharp, hΛWdef, hΛξdef, hGdef]
      simp only [hexpand]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hPwdef, ← hPedef, ← hPcdef]
    -- W exponent budget (NON-boundary): wb = (t+2)+(d-2).
    -- E1 leftover: eta^(E1 - Pe).
    -- Every lifted Z-coefficient has weight at most `D-j` directly from the Y/Z cap.
    have hcoeffW : RegularWeightLe hH
        ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1) D (D - j) := by
      apply regularWeightLe_shiftedCoeff_yz hD_H hH x₀ (R.coeff j) _ p.1
      intro a ha
      have := hYZ j a ha
      omega
    have htd_le : D - j ≤ D - j := le_rfl
    -- key arithmetic facts
    have hkey : D ≤ R.natDegree + ΛW := by
      rw [hΛWdef]
      have : Bivariate.natDegreeY H ≤ R.natDegree := by rw [← hdY]; exact hdH_le_R
      rw [hdH] at this
      omega
    have hjd : j ≤ R.natDegree := hjle
    have hdD : R.natDegree ≤ D := by
      by_cases hRz : R = 0
      · simp [hRz]
      · have hlc : R.coeff R.natDegree ≠ 0 := by
          have hh := Polynomial.leadingCoeff_ne_zero.mpr hRz
          rw [Polynomial.leadingCoeff] at hh
          exact hh
        obtain ⟨a, ha⟩ : ∃ a, (R.coeff R.natDegree).coeff a ≠ 0 := by
          by_contra hn
          push_neg at hn
          apply hlc
          apply Polynomial.ext
          intro n
          exact hn n
        have := hYZ R.natDegree a ha
        omega
    have hjD : j ≤ D := le_trans hjd hdD
    -- boundary detection
    by_cases hbdry : p.2 = t + 1 ∧ j = R.natDegree ∧ 2 ≤ R.natDegree
    · -- BOUNDARY CASE: `p.1 = 0`, `j = d = R.natDegree ≥ 2`, `p.2 = t+1`.
      --
      -- The `d` part-certificates consume `Pw = p.2 + j = t+d+1` factors of `W`, one more than the
      -- `wb = (t+2) + (d-2) = t+d` the goal supplies.  The missing factor comes from the
      -- leading-coefficient divisibility `W ∣ leadingCoeff R(x₀,·,Z)`
      -- (`leadingCoeff_dvd_evalX_coeff_natDegree`): writing that coefficient as `W * c` turns the
      -- coefficient charge from `D - d` into `Λ(c) = c.natDegree ≤ D - d`, and frees the `W`.
      --
      -- The resulting deficit is exactly `c.natDegree`, and it is paid by the correction term of
      -- `numeratorShapeSharp`: this branch forces `p.2 = t+1` split into parts each `≤ t`, hence at
      -- least two nonzero parts, so the parts consume at most `Pc ≤ t-1` of the correction while
      -- the target provides `t`, leaving `(S₁-1)·G ≥ G = D - dY ≥ c.natDegree`.  See the
      -- docstring of `numeratorShapeSharp` for why the paper's uncorrected form is not provable
      -- here.
      obtain ⟨hb2, hjd', hd2⟩ := hbdry
      have hp1 : p.1 = 0 := by omega
      -- at least two nonzero parts, since each part is `≤ t` but they sum to `t+1`
      have hS1ge : 2 ≤ S1 := by
        by_contra h
        push Not at h
        interval_cases S1 <;> omega
      have hPc_lt : Pc + 1 ≤ t := by omega
      -- the boundary coefficient is `W * c`
      have hdvd : H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree :=
        leadingCoeff_dvd_evalX_coeff_natDegree hHyp
      obtain ⟨c, hc⟩ := hdvd
      have hcoeff_eq : (R.coeff R.natDegree).eval (Polynomial.C x₀) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
        simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
      have hW_ne : H.leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hH)
      -- `c.natDegree ≤ G = D - dY`, since `W * c` is a coefficient of `R(x₀,·,Z)`
      have hc_deg : c.natDegree ≤ G := by
        rw [hGdef]
        by_cases hc0 : c = 0
        · rw [hc0]; simp
        · have hne : (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree ≠ 0 := by
            rw [hc]; exact mul_ne_zero hW_ne hc0
          have hle' : c.natDegree ≤
              ((Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree).natDegree := by
            refine Polynomial.natDegree_le_of_dvd ?_ hne
            exact hc ▸ Dvd.intro_left _ rfl
          have hbound : ((Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree).natDegree ≤
              D - R.natDegree :=
            natDegree_coeff_le_of_totalDegree_le _ hD_Rx0 R.natDegree
          rw [hdY]; omega
      -- rewrite the coefficient factor as `W * lift c`
      have hcoeff_split :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 =
            W * liftToFunctionField (H := H) c := by
        rw [hp1, hjd', shiftedCoeffPolynomial_coeff_zero, hcoeff_eq, hc, map_mul, hWdef]
      -- the freed `W` completes `W^Pw`, so the parts certificate applies verbatim
      have hPweq' : Pw = t + 1 + R.natDegree := by rw [hPweq, hb2, hjd']
      have hreassoc :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          liftToFunctionField (H := H) c *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            eta ^ (E1 - Pe) := by
        rw [hcoeff_split, hPweq']
        have hWpow : W * (W ^ (t + 1 + 1) * W ^ (R.natDegree - 2)) = W ^ (t + 1 + R.natDegree) := by
          rw [← pow_add, ← pow_succ']
          congr 1
          omega
        have hEpow : eta ^ E1 = eta ^ Pe * eta ^ (E1 - Pe) := by
          rw [← pow_add]
          congr 1
          omega
        calc W * liftToFunctionField (H := H) c *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2))
            = liftToFunctionField (H := H) c * (∏ i ∈ Finset.range j, αtrunc (l i)) *
                ((W * (W ^ (t + 1 + 1) * W ^ (R.natDegree - 2))) * eta ^ E1) := by ring
          _ = liftToFunctionField (H := H) c * (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + R.natDegree) * (eta ^ Pe * eta ^ (E1 - Pe))) := by
                rw [hWpow, hEpow]
          _ = liftToFunctionField (H := H) c *
                ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                  (W ^ (t + 1 + R.natDegree) * eta ^ Pe)) * eta ^ (E1 - Pe) := by ring
      rw [hreassoc]
      refine (RegularWeightLe.mul hD_H
        (RegularWeightLe.mul hD_H
          ((regularWeightLe_liftToFunctionField hD_H hH c).mono hc_deg) hprodW)
        (hRWLeta.pow hD_H _)).mono ?_
      rw [hsharpSum]
      have hsharpSucc : numeratorShapeSharp R H D (t + 1) =
          1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by
        rw [numeratorShapeSharp, ← hΛWdef, ← hΛξdef, ← hGdef, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
        rw [show t + 1 + 1 = t + 2 by omega,
          show t + 1 - 1 = t by omega]
      rw [hsharpSucc]
      -- `Λξ = (dY-1)·(ΛW+1)` and `G = D - dY`, so the whole thing is linear arithmetic
      have hΛξval : Λξ = (R.natDegree - 1) * (ΛW + 1) := by rw [hΛξdef, hΛWdef, hdY]
      have hGval : G = D - R.natDegree := by rw [hGdef, hdY]
      have hE1val : E1 = 2 * t := by rw [hE1def, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      -- expand the two products so that only `ΛW`-linear atoms remain
      obtain ⟨dm, hdmeq⟩ : ∃ dm, R.natDegree = dm + 2 := ⟨R.natDegree - 2, by omega⟩
      have hΛξexp : Λξ = dm * ΛW + dm + ΛW + 1 := by
        rw [hΛξval, hdmeq, show dm + 2 - 1 = dm + 1 by omega]; ring
      have hPwexp : Pw * ΛW = (t + 1) * ΛW + dm * ΛW + 2 * ΛW := by
        rw [hPweq', hdmeq]; ring
      have hPeval : Pe * Λξ + (E1 - Pe) * Λξ = 2 * t * Λξ := by
        rw [← Nat.add_mul, hE1val]; congr 1; omega
      have hPcG : G + Pc * G ≤ t * G := by
        calc G + Pc * G = (Pc + 1) * G := by ring
          _ ≤ t * G := Nat.mul_le_mul_right _ hPc_lt
      -- everything but `G + Pc·G ≤ t·G` is a ring identity: the `W`- and `ξ`-charges match exactly
      calc G + (j + Pw * ΛW + Pe * Λξ + Pc * G) + (E1 - Pe) * Λξ
          = (j + Pw * ΛW + (Pe * Λξ + (E1 - Pe) * Λξ)) + (G + Pc * G) := by ring
        _ = (j + Pw * ΛW + E1 * Λξ) + (G + Pc * G) := by
              rw [← Nat.add_mul, Nat.add_sub_cancel' hPe_le]
        _ ≤ (j + Pw * ΛW + E1 * Λξ) + t * G := Nat.add_le_add_left hPcG _
        _ = 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by
              rw [hjd', hPweq', hE1val, hΛξexp, hdmeq]; ring
    · -- NON-BOUNDARY: budget Pw ≤ (t+2)+(d-2) covers everything.
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) := by
        rw [hPweq, Finset.mem_range] at *
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · omega
        · rcases not_and_or.mp hbdry with h1 | h2
          · omega
          · rcases not_and_or.mp h2 with h3 | h4
            · omega
            · exact absurd hd h4
      -- reassociate to isolate W^(wb-Pw) and eta^(E1-Pe)
      have hreassoc :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2)) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2)) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2)) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ ((t + 1 + 1) + (R.natDegree - 2)) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      refine (RegularWeightLe.mul hD_H
        (RegularWeightLe.mul hD_H (hcoeffW.mono htd_le) hprodW)
        (RegularWeightLe.mul hD_H (hRWLW.pow hD_H _) (hRWLeta.pow hD_H _))).mono ?_
      -- weight: (D-j) + (j + Pw*ΛW + Pe*Λξ) + ((wb-Pw)*ΛW + (E1-Pe)*Λξ) ≤ sharp(t+1)
      rw [hsharpSum]
      -- sharp(t+1) expansion
      have hsharpSucc : numeratorShapeSharp R H D (t + 1) =
          1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by
        rw [numeratorShapeSharp, ← hΛWdef, ← hΛξdef, ← hGdef, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
        rw [show t + 1 + 1 = t + 2 by omega,
          show t + 1 - 1 = t by omega]
      rw [hsharpSucc]
      -- now pure arithmetic (verified separately)
      set wb := (t + 1 + 1) + (R.natDegree - 2) with hwbdef
      have hE1val : E1 = 2 * t := by rw [hE1def, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      have hwb_le : wb ≤ t + R.natDegree := by
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · -- d < 2: then not boundary forces nothing, but budget? wb = (t+2)+0 = t+2
          rw [hwbdef]; omega
        · rw [hwbdef]; omega
      -- reduce via cancellations
      have hAcancel : Pw * ΛW + (wb - Pw) * ΛW = wb * ΛW := by
        rw [← Nat.add_mul]; congr 1; omega
      have hBcancel : Pe * Λξ + (E1 - Pe) * Λξ = E1 * Λξ := by
        rw [← Nat.add_mul]; congr 1; omega
      have hjDj : D - j + j = D := Nat.sub_add_cancel hjD
      -- Final: (D-j) + (j + Pw ΛW + Pe Λξ) + ((wb-Pw)ΛW + (E1-Pe)Λξ) = D + wb*ΛW + E1*Λξ
      have hΛξval : Λξ = (R.natDegree - 1) * (ΛW + 1) := by
        rw [hΛξdef, hΛWdef, hdY]
      -- prove ≤
      have hfin0 : (D - j) + (j + Pw * ΛW + Pe * Λξ) +
          ((wb - Pw) * ΛW + (E1 - Pe) * Λξ) ≤ 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ := by
        have e1 : (D - j) + (j + Pw * ΛW + Pe * Λξ) + ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)
            = D + wb * ΛW + E1 * Λξ := by
          rw [← hjDj] at *
          -- use cancellations
          have := hAcancel; have := hBcancel
          omega
        rw [e1, hE1val, hΛξval]
        -- D + wb*ΛW + 2t*((d-1)(ΛW+1)) ≤ 1 + (t+2)ΛW + (2t+1)((d-1)(ΛW+1))
        obtain ⟨gap, hgap⟩ : ∃ g, t + R.natDegree = wb + g := ⟨t + R.natDegree - wb, by omega⟩
        obtain ⟨dm, hdmeq⟩ : ∃ dm, R.natDegree = dm + 1 := ⟨R.natDegree - 1, by
          rcases Nat.lt_or_ge R.natDegree 2 with h | h
          · -- d < 2 ⇒ d ≤ 1; need d ≥ 1: R.natDegree ≥ natDegreeY H ≥ 1
            have : 1 ≤ R.natDegree := by rw [← hdY]; rw [← hdH] at *; omega
            omega
          · omega⟩
        rw [hdmeq] at hkey ⊢
        rw [show dm + 1 - 1 = dm by omega]
        nlinarith [hkey, hwb_le, hgap, Nat.mul_le_mul_right ΛW hwb_le]
      -- the correction the parts consume is at most the `t·G` the target provides
      calc (D - j) + (j + Pw * ΛW + Pe * Λξ + Pc * G) +
            ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)
          = ((D - j) + (j + Pw * ΛW + Pe * Λξ) + ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)) + Pc * G := by
            ring
        _ ≤ (1 + (t + 2) * ΛW + (2 * t + 1) * Λξ) + t * G :=
            Nat.add_le_add hfin0 (Nat.mul_le_mul_right _ hPc_le)
        _ = 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ + t * G := by ring



lemma finiteHenselClearedResidual_weight
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (t : ℕ) (αtrunc : ℕ → 𝕃 H)
    (ihNum : ∀ i, i ≤ t → RegularWeightLe hH
      (αtrunc i * (Wfield (H := H) ^ (i + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i))
      D (numeratorShapeSharp R H D i))
    (hαzero : ∀ i, t < i → αtrunc i = 0) :
    RegularWeightLe hH
      ((ProximityPrize.SubmissionLower.FiniteHensel.residual
        (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) αtrunc t).coeff (t + 1) *
        (Wfield (H := H) ^ (t + 1 + 1) *
          etaField (R := R) (H := H) x₀ hHyp ^
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
          Wfield (H := H) ^ (R.natDegree - 2)))
      D (numeratorShapeSharp R H D (t + 1)) := by
  classical
  unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
  rw [Polynomial.eval₂_eq_sum_range]
  have hcoeff :
      (∑ i ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
          (fieldTo𝕃 (H := H) x₀) ((liftedR (R := R) (H := H)).coeff i) *
          ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t ^ i).coeff (t + 1) =
      ∑ i ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        (ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
          (fieldTo𝕃 (H := H) x₀) ((liftedR (R := R) (H := H)).coeff i) *
          ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t ^ i).coeff (t + 1) := by simp
  rw [hcoeff, Finset.sum_mul]
  refine RegularWeightLe.sum _ _ hD_H ?_
  intro j hjlift
  have hj : j ∈ Finset.range (R.natDegree + 1) := by
    rw [Finset.mem_range] at hjlift ⊢
    have hmap : (liftedR (R := R) (H := H)).natDegree ≤ R.natDegree :=
      Polynomial.natDegree_map_le
    omega
  have hcoeffmap : (liftedR (R := R) (H := H)).coeff j =
      (R.coeff j).map (liftToFunctionField (H := H)) := by
    simp [liftedR, Polynomial.coeff_map]
  rw [hcoeffmap]
  change RegularWeightLe hH
    (((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) *
      (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t) ^ j).coeff (t + 1) *
      (Wfield (H := H) ^ (t + 1 + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
        Wfield (H := H) ^ (R.natDegree - 2)))) D _
  exact finiteHenselClearedTerm_weight x₀ R H hHyp hH hD_H hD_R hD_Rx0 hRdeg
    t αtrunc ihNum hαzero j hj



lemma finiteHenselClearedResidual_weight_yz
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (t : ℕ) (αtrunc : ℕ → 𝕃 H)
    (ihNum : ∀ i, i ≤ t → RegularWeightLe hH
      (αtrunc i * (Wfield (H := H) ^ (i + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i))
      D (numeratorShapeSharp R H D i))
    (hαzero : ∀ i, t < i → αtrunc i = 0) :
    RegularWeightLe hH
      ((ProximityPrize.SubmissionLower.FiniteHensel.residual
        (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) αtrunc t).coeff (t + 1) *
        (Wfield (H := H) ^ (t + 1 + 1) *
          etaField (R := R) (H := H) x₀ hHyp ^
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
          Wfield (H := H) ^ (R.natDegree - 2)))
      D (numeratorShapeSharp R H D (t + 1)) := by
  classical
  unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
  rw [Polynomial.eval₂_eq_sum_range]
  have hcoeff :
      (∑ i ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
          (fieldTo𝕃 (H := H) x₀) ((liftedR (R := R) (H := H)).coeff i) *
          ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t ^ i).coeff (t + 1) =
      ∑ i ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        (ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
          (fieldTo𝕃 (H := H) x₀) ((liftedR (R := R) (H := H)).coeff i) *
          ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t ^ i).coeff (t + 1) := by simp
  rw [hcoeff, Finset.sum_mul]
  refine RegularWeightLe.sum _ _ hD_H ?_
  intro j hjlift
  have hj : j ∈ Finset.range (R.natDegree + 1) := by
    rw [Finset.mem_range] at hjlift ⊢
    have hmap : (liftedR (R := R) (H := H)).natDegree ≤ R.natDegree :=
      Polynomial.natDegree_map_le
    omega
  have hcoeffmap : (liftedR (R := R) (H := H)).coeff j =
      (R.coeff j).map (liftToFunctionField (H := H)) := by
    simp [liftedR, Polynomial.coeff_map]
  rw [hcoeffmap]
  change RegularWeightLe hH
    (((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) *
      (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t) ^ j).coeff (t + 1) *
      (Wfield (H := H) ^ (t + 1 + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
        Wfield (H := H) ^ (R.natDegree - 2)))) D _
  exact finiteHenselClearedTerm_weight_yz x₀ R H hHyp hH hD_H hYZ hD_Rx0 hRdeg
    t αtrunc ihNum hαzero j hj


lemma truncSeries_coeff_eq (p : (𝕃 H)[X]) (N : ℕ) (hdeg : p.natDegree ≤ N) :
    ProximityPrize.SubmissionLower.FiniteHensel.truncSeries (fun i => p.coeff i) N = p := by
  ext i
  by_cases hi : i ≤ N
  · rw [ProximityPrize.SubmissionLower.FiniteHensel.coeff_truncSeries _ _ _ hi]
  · have hp : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hp]
    simp [ProximityPrize.SubmissionLower.FiniteHensel.truncSeries,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi]


lemma evalX_totalDegree_le_of_coeff_bound_finite (x₀ : F) (R : F[X][X][Y]) {D : ℕ}
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := by
  classical
  unfold Bivariate.totalDegree
  refine Finset.sup_le ?_
  intro i hi
  have hcoeff_ne : (Bivariate.evalX (Polynomial.C x₀) R).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  have hRi : i ∈ R.support := by
    apply Polynomial.mem_support_iff.mpr
    intro h0
    apply hcoeff_ne
    simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, h0]
  have heval : ((Bivariate.evalX (Polynomial.C x₀) R).coeff i).natDegree ≤
      Bivariate.totalDegree (R.coeff i) := by
    rw [show (Bivariate.evalX (Polynomial.C x₀) R).coeff i =
      (R.coeff i).eval (Polynomial.C x₀) by
        simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]]
    exact (Bivariate.degree_eval_le_weightedDegree (Q := R.coeff i)
      (P := Polynomial.C x₀) (k := 1) (by simp)).trans (by
        unfold Bivariate.natWeightedDegree Bivariate.totalDegree
        simp only [Nat.sub_self, one_mul, zero_mul, add_zero]
        refine Finset.sup_le ?_
        intro j hj
        exact le_trans (Nat.le_add_right _ _) (Finset.le_sup (f := fun m =>
          ((R.coeff i).coeff m).natDegree + m) hj))
  have := hD_R i hRi
  omega


lemma evalX_totalDegree_le_of_yzCap (x₀ : F) (R : F[X][X][Y]) {D : ℕ}
    (hYZ : YZCap R D) :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := by
  classical
  unfold Bivariate.totalDegree
  refine Finset.sup_le ?_
  intro i hi
  have heval : ((Bivariate.evalX (Polynomial.C x₀) R).coeff i).natDegree ≤ D - i := by
    rw [show (Bivariate.evalX (Polynomial.C x₀) R).coeff i =
      (R.coeff i).eval (Polynomial.C x₀) by
        simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]]
    refine (Bivariate.degree_eval_le_weightedDegree (Q := R.coeff i)
      (P := Polynomial.C x₀) (k := 0) (by simp)).trans ?_
    unfold Bivariate.natWeightedDegree
    refine Finset.sup_le ?_
    intro a ha
    have hne : (R.coeff i).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
    have := hYZ i a hne
    omega
  have hcoeff_ne : (Bivariate.evalX (Polynomial.C x₀) R).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  have hRi : R.coeff i ≠ 0 := by
    intro hz
    apply hcoeff_ne
    simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hz]
  obtain ⟨a, ha⟩ : ∃ a, (R.coeff i).coeff a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hRi
    apply Polynomial.ext
    intro a
    exact hn a
  have hiD := hYZ i a ha
  omega

/-- Sharp weight induction for the concrete diagonal numerators. -/
theorem betaDiagonal_weight_sharp
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) (N : ℕ) :
    ∀ t, t ≤ N → RegularWeightLe hH
      (betaDiagonal (R := R) (H := H) x₀ hHyp N t) D
      (numeratorShapeSharp R H D t) := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          have hW : Wfield (H := H) ≠ 0 := Wfield_ne_zero (H := H)
          have hb0 : betaDiagonal (R := R) (H := H) x₀ hHyp N 0 =
              functionFieldT (H := H) := by
            unfold betaDiagonal alphaDiagonal
            simp only [ProximityPrize.SubmissionLower.FiniteHensel.liftPoly,
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_zero,
              pow_zero, mul_one, zero_add, pow_one, Polynomial.coeff_C_zero]
            unfold initialValue Wfield
            rw [div_mul_cancel₀ _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))]
          rw [hb0]
          refine ⟨(Ideal.Quotient.mk (Ideal.span {monicize H})
            (Polynomial.X : F[X][Y]) : 𝒪 H), ?_, ?_⟩
          · rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]
          · refine (regularWeight_mk_le hD_H hH (Polynomial.X : F[X][Y])).trans ?_
            have hX : weight (Polynomial.X : F[X][Y]) H D ≤
                (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
              simpa only [pow_one, one_mul] using
                (weight_X_pow_le (H := H) (D := D) (k := 1))
            refine hX.trans ?_
            rw [WithBot.coe_le_coe]
            unfold numeratorShapeSharp
            rw [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_zero]
            omega
      | succ m =>
          let oldp := ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
            (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
            (initialValue (H := H)) N m
          let old : ℕ → 𝕃 H := fun i => oldp.coeff i
          have hmN : m ≤ N := by omega
          have hdeg : oldp.natDegree ≤ m := liftPoly_natDegree_le (R := R) (H := H) x₀ N m
          have holdzero : ∀ i, m < i → old i = 0 := by
            intro i hi
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have ihNum : ∀ i, i ≤ m → RegularWeightLe hH
              (old i * (Wfield (H := H) ^ (i + 1) *
                etaField (R := R) (H := H) x₀ hHyp ^
                  ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i))
              D (numeratorShapeSharp R H D i) := by
            intro i hi
            have hdiag := liftPoly_coeff_eq_diagonal (R := R) (H := H) x₀ N m i hi
            have hiw := ih i (by omega) (by omega)
            change old i = alphaDiagonal (R := R) (H := H) x₀ N i at hdiag
            rw [hdiag]
            exact hiw
          have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) :=
            evalX_totalDegree_le_of_coeff_bound_finite x₀ R hD_R
          have hreg := finiteHenselClearedResidual_weight x₀ R H hHyp hH hD_H hD_R
            hD_Rx0 hRdeg m old ihNum holdzero
          have htruncN : ProximityPrize.SubmissionLower.FiniteHensel.truncSeries old N = oldp :=
            truncSeries_coeff_eq (H := H) oldp N (hdeg.trans hmN)
          have htruncm : ProximityPrize.SubmissionLower.FiniteHensel.truncSeries old m = oldp :=
            truncSeries_coeff_eq (H := H) oldp m hdeg
          have herr :
              (ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) =
              (ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old m).coeff (m + 1) := by
            unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
            rw [htruncN, htruncm]
          rw [← herr] at hreg
          have holdtop : old (m + 1) = 0 := holdzero _ (by omega)
          have hnew : alphaDiagonal (R := R) (H := H) x₀ N (m + 1) =
              -((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1)) /
                zeta R x₀ H := by
            have hs := ProximityPrize.SubmissionLower.FiniteHensel.liftPoly_succ_coeff_sub
              (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
              (initialValue (H := H)) N m
            change alphaDiagonal (R := R) (H := H) x₀ N (m + 1) - old (m + 1) = _ at hs
            rw [holdtop, sub_zero, ySlope_liftedR_eq_zeta] at hs
            exact hs
          have hbeta : betaDiagonal (R := R) (H := H) x₀ hHyp N (m + 1) =
              -((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) *
                (Wfield (H := H) ^ (m + 1 + 1) *
                  etaField (R := R) (H := H) x₀ hHyp ^
                    (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1) *
                  Wfield (H := H) ^ (R.natDegree - 2))) := by
            unfold betaDiagonal
            rw [hnew, etaField_eq]
            have hepos : 0 < ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) := by
              rw [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
              omega
            rw [show ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) =
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1) + 1 by omega,
              pow_succ]
            field_simp [hzeta]
            rw [show ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1 + 1 - 1 =
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1 by omega]
            rw [pow_succ]
            ring
          rw [hbeta]
          exact RegularWeightLe.neg hreg

/-- Finite-polynomial analogue of coefficientwise regularity. -/

theorem betaDiagonal_weight_sharp_yz
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) (N : ℕ) :
    ∀ t, t ≤ N → RegularWeightLe hH
      (betaDiagonal (R := R) (H := H) x₀ hHyp N t) D
      (numeratorShapeSharp R H D t) := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          have hW : Wfield (H := H) ≠ 0 := Wfield_ne_zero (H := H)
          have hb0 : betaDiagonal (R := R) (H := H) x₀ hHyp N 0 =
              functionFieldT (H := H) := by
            unfold betaDiagonal alphaDiagonal
            simp only [ProximityPrize.SubmissionLower.FiniteHensel.liftPoly,
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_zero,
              pow_zero, mul_one, zero_add, pow_one, Polynomial.coeff_C_zero]
            unfold initialValue Wfield
            rw [div_mul_cancel₀ _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))]
          rw [hb0]
          refine ⟨(Ideal.Quotient.mk (Ideal.span {monicize H})
            (Polynomial.X : F[X][Y]) : 𝒪 H), ?_, ?_⟩
          · rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]
          · refine (regularWeight_mk_le hD_H hH (Polynomial.X : F[X][Y])).trans ?_
            have hX : weight (Polynomial.X : F[X][Y]) H D ≤
                (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
              simpa only [pow_one, one_mul] using
                (weight_X_pow_le (H := H) (D := D) (k := 1))
            refine hX.trans ?_
            rw [WithBot.coe_le_coe]
            unfold numeratorShapeSharp
            rw [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_zero]
            omega
      | succ m =>
          let oldp := ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
            (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
            (initialValue (H := H)) N m
          let old : ℕ → 𝕃 H := fun i => oldp.coeff i
          have hmN : m ≤ N := by omega
          have hdeg : oldp.natDegree ≤ m := liftPoly_natDegree_le (R := R) (H := H) x₀ N m
          have holdzero : ∀ i, m < i → old i = 0 := by
            intro i hi
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have ihNum : ∀ i, i ≤ m → RegularWeightLe hH
              (old i * (Wfield (H := H) ^ (i + 1) *
                etaField (R := R) (H := H) x₀ hHyp ^
                  ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i))
              D (numeratorShapeSharp R H D i) := by
            intro i hi
            have hdiag := liftPoly_coeff_eq_diagonal (R := R) (H := H) x₀ N m i hi
            have hiw := ih i (by omega) (by omega)
            change old i = alphaDiagonal (R := R) (H := H) x₀ N i at hdiag
            rw [hdiag]
            exact hiw
          have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) :=
            evalX_totalDegree_le_of_yzCap x₀ R hYZ
          have hreg := finiteHenselClearedResidual_weight_yz x₀ R H hHyp hH hD_H hYZ
            hD_Rx0 hRdeg m old ihNum holdzero
          have htruncN : ProximityPrize.SubmissionLower.FiniteHensel.truncSeries old N = oldp :=
            truncSeries_coeff_eq (H := H) oldp N (hdeg.trans hmN)
          have htruncm : ProximityPrize.SubmissionLower.FiniteHensel.truncSeries old m = oldp :=
            truncSeries_coeff_eq (H := H) oldp m hdeg
          have herr :
              (ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) =
              (ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old m).coeff (m + 1) := by
            unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
            rw [htruncN, htruncm]
          rw [← herr] at hreg
          have holdtop : old (m + 1) = 0 := holdzero _ (by omega)
          have hnew : alphaDiagonal (R := R) (H := H) x₀ N (m + 1) =
              -((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1)) /
                zeta R x₀ H := by
            have hs := ProximityPrize.SubmissionLower.FiniteHensel.liftPoly_succ_coeff_sub
              (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
              (initialValue (H := H)) N m
            change alphaDiagonal (R := R) (H := H) x₀ N (m + 1) - old (m + 1) = _ at hs
            rw [holdtop, sub_zero, ySlope_liftedR_eq_zeta] at hs
            exact hs
          have hbeta : betaDiagonal (R := R) (H := H) x₀ hHyp N (m + 1) =
              -((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) *
                (Wfield (H := H) ^ (m + 1 + 1) *
                  etaField (R := R) (H := H) x₀ hHyp ^
                    (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1) *
                  Wfield (H := H) ^ (R.natDegree - 2))) := by
            unfold betaDiagonal
            rw [hnew, etaField_eq]
            have hepos : 0 < ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) := by
              rw [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
              omega
            rw [show ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) =
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1) + 1 by omega,
              pow_succ]
            field_simp [hzeta]
            rw [show ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1 + 1 - 1 =
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1 by omega]
            rw [pow_succ]
            ring
          rw [hbeta]
          exact RegularWeightLe.neg hreg

/-- Finite-polynomial analogue of coefficientwise regularity. -/
def AllCoeffRegularPoly (H : F[X][Y]) (p : (𝕃 H)[X]) : Prop :=
  ∀ n, p.coeff n ∈ regularElementsSet H

lemma AllCoeffRegularPoly.add {p q : (𝕃 H)[X]}
    (hp : AllCoeffRegularPoly H p) (hq : AllCoeffRegularPoly H q) :
    AllCoeffRegularPoly H (p + q) := by
  intro n
  rw [Polynomial.coeff_add]
  exact regularElementsSet_add (hp n) (hq n)

lemma AllCoeffRegularPoly.mul {p q : (𝕃 H)[X]}
    (hp : AllCoeffRegularPoly H p) (hq : AllCoeffRegularPoly H q) :
    AllCoeffRegularPoly H (p * q) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply regularElementsSet_sum
  intro ij hij
  exact regularElementsSet_mul (hp ij.1) (hq ij.2)

lemma AllCoeffRegularPoly.pow {p : (𝕃 H)[X]}
    (hp : AllCoeffRegularPoly H p) (m : ℕ) :
    AllCoeffRegularPoly H (p ^ m) := by
  induction m with
  | zero =>
      intro n
      simp only [pow_zero]
      by_cases hn : n = 0
      · subst n
        simpa using regularElementsSet_one H
      · rw [Polynomial.coeff_one]
        simp only [if_neg hn]
        exact regularElementsSet_zero H
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul hp

lemma AllCoeffRegularPoly.C {c : 𝕃 H} (hc : c ∈ regularElementsSet H) :
    AllCoeffRegularPoly H (Polynomial.C c) := by
  intro n
  rw [Polynomial.coeff_C]
  split
  · exact hc
  · exact regularElementsSet_zero H

lemma AllCoeffRegularPoly.X :
    AllCoeffRegularPoly H (Polynomial.X : (𝕃 H)[X]) := by
  intro n
  rw [Polynomial.coeff_X]
  split
  · exact regularElementsSet_one H
  · exact regularElementsSet_zero H

lemma fieldToL_regular (x₀ : F) :
    fieldTo𝕃 (H := H) x₀ ∈ regularElementsSet H := by
  change RingHom.comp (liftToFunctionField (H := H)) Polynomial.C x₀ ∈ regularElementsSet H
  rw [RingHom.comp_apply]
  exact regularElementsSet_liftToFunctionField H _

/-- Every coefficient of a shifted/lifted coefficient polynomial is regular. -/
theorem coeff_shifted_regular (x₀ : F) (p : F[X][X]) :
    AllCoeffRegularPoly H
      (ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
        (fieldTo𝕃 (H := H) x₀)
        (p.map (liftToFunctionField (H := H)))) := by
  classical
  rw [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply]
  change AllCoeffRegularPoly H
    (Polynomial.eval₂ (Polynomial.C : 𝕃 H →+* (𝕃 H)[X])
      (Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X)
      (p.map (liftToFunctionField (H := H))))
  rw [Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_induction _ (AllCoeffRegularPoly H)
    (fun _ _ => AllCoeffRegularPoly.add) (by
      intro n
      rw [Polynomial.coeff_zero]
      exact regularElementsSet_zero H)
  intro n hn
  have hc : (p.map (liftToFunctionField (H := H))).coeff n ∈ regularElementsSet H := by
    rw [Polynomial.coeff_map]
    exact regularElementsSet_liftToFunctionField H _
  exact AllCoeffRegularPoly.mul
    (AllCoeffRegularPoly.C hc)
    ((AllCoeffRegularPoly.add (AllCoeffRegularPoly.C (fieldToL_regular (H := H) x₀))
      (AllCoeffRegularPoly.X (H := H))).pow n)


theorem finiteHenselClearedTerm_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0) (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (αtrunc : ℕ → 𝕃 H)
    (hshape : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
          (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
            (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)
      else 0)
    (j : ℕ) (hj : j ∈ Finset.range (R.natDegree + 1)) :
    (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) * (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t) ^ j).coeff (t + 1) *
      (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
        (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
        liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)) ∈
      regularElementsSet H := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) with hetadef
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hetane : eta ≠ 0 := by
    rw [hetadef, embeddingOf𝒪Into𝕃_xi]
    exact mul_ne_zero (pow_ne_zero _ hWne) (hzeta)
  have hjle : j ≤ R.natDegree := by
    rw [Finset.mem_range] at hj; omega
  -- regularity of cleared numerators (clearing the denominator of each `αtrunc i`, `i ≤ t`)
  have hnumReg : ∀ i, i ≤ t →
      αtrunc i * (W ^ (i + 1) * eta ^ ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) ∈ regularElementsSet H := by
    intro i hi
    rw [hshape i, dif_pos hi, hWdef, hetadef,
      div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hWne) (pow_ne_zero _ hetane))]
    exact ⟨βprev ⟨i, by omega⟩, rfl⟩
  -- `αtrunc` vanishes above the truncation point
  have hαzero : ∀ i, t < i → αtrunc i = 0 := by
    intro i hi; rw [hshape i, dif_neg (by omega)]
  -- Step: distribute `coeff_mul` and `coeff_pow`, reduce to a single composition `l`.
  rw [Polynomial.coeff_mul, Finset.sum_mul]
  apply regularElementsSet_sum
  intro p _hp
  rw [polynomial_coeff_pow]
  simp only [coeff_truncSeries_eq_if]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply regularElementsSet_sum
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hcoeffReg : (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1
      ∈ regularElementsSet H := coeff_shifted_regular (H := H) x₀ (R.coeff j) p.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp _hp
  -- Case A: some part exceeds `t`  ⇒  the product has a zero factor.
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j,
        if l i ≤ t then αtrunc (l i) else 0) = 0 := by
      apply Finset.prod_eq_zero hi₀
      rw [if_neg (by omega)]
    rw [hz]
    simp
  · -- Case B: all parts `≤ t`.
    push Not at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    have hprod_if : (∏ i ∈ Finset.range j,
        if l i ≤ t then αtrunc (l i) else 0) =
        ∏ i ∈ Finset.range j, αtrunc (l i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_pos (hle i hi)]
    rw [hprod_if]
    -- product-clearing: `(∏ αtrunc) · W^{∑(lᵢ+1)} · eta^{∑e} ∈ regular`
    have hprodReg : (∏ i ∈ Finset.range j, αtrunc (l i)) *
        (W ^ (∑ i ∈ Finset.range j, (l i + 1)) *
          eta ^ (∑ i ∈ Finset.range j, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)))
        ∈ regularElementsSet H := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact regularElementsSet_prod _ fun i hi => hnumReg (l i) (hle i hi)
    -- the eta exponent bound `∑ e ≤ E - 1 = 2t`
    have hPe : (∑ i ∈ Finset.range j, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) ≤
        ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1 := by
      set Pe := (∑ i ∈ Finset.range j, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) with hPedef
      set S1 := (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) with hS1def
      have h2b : 2 * p.2 = Pe + S1 := by
        rw [hPedef, hS1def, ← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          by_cases hi : l i = 0 <;>
            simp [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent, hi] <;> omega
      have hbS1 : p.2 ≤ t * S1 := by
        rw [← hbsum, hS1def, Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        split
        · next h => rw [h]; simp
        · next h => rw [Nat.mul_one]; exact hle i hi
      have hE1 : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1 = 2 * t := by
        rw [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]; omega
      rw [hE1]
      rcases Nat.lt_or_ge p.2 (t + 1) with hbt | hbt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h
          push Not at h
          interval_cases S1 <;> omega
        omega
    -- `Pw = ∑(lᵢ + 1) = p.2 + j`
    have hPweq : (∑ i ∈ Finset.range j, (l i + 1)) = p.2 + j := by
      rw [Finset.sum_add_distrib, hbsum]; simp
    set Pw := (∑ i ∈ Finset.range j, (l i + 1)) with hPwdef
    set Pe := (∑ i ∈ Finset.range j, ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (l i)) with hPedef
    set E1 := ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1 with hE1def
    -- helper: given a `W`-budget `wb ≥ Pw` and a regular `cf`, finish.
    have finish_with : ∀ (cf : 𝕃 H) (wb : ℕ),
        cf ∈ regularElementsSet H → Pw ≤ wb →
        cf * ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
          (W ^ (wb - Pw) * eta ^ (E1 - Pe)) ∈ regularElementsSet H := by
      intro cf wb hcf _hwb
      refine regularElementsSet_mul (regularElementsSet_mul hcf hprodReg) ?_
      exact regularElementsSet_mul
        (by rw [hWdef]; exact regularElementsSet_pow (regularElementsSet_liftToFunctionField H _) _)
        (by rw [hetadef]; exact regularElementsSet_pow ⟨_, rfl⟩ _)
    -- boundary detection
    by_cases hbdry : p.2 = t + 1 ∧ j = R.natDegree ∧ 2 ≤ R.natDegree
    · -- boundary: `p.1 = 0`, `j = d`, `d ≥ 2`; one extra `W` comes from the leading-coeff
      -- divisibility `W ∣ coeff 0 (liftCoeff (R.coeff d))`.
      obtain ⟨hb, hjeq, hdge⟩ := hbdry
      have ha0 : p.1 = 0 := by omega
      -- coeff 0 (liftCoeff (R.coeff d)) = W * q, q regular
      have hWdvd : ∃ q : 𝕃 H, q ∈ regularElementsSet H ∧
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 = W * q := by
        rw [ha0, hjeq, shiftedCoeffPolynomial_coeff_zero]
        have hcoeff : (R.coeff R.natDegree).eval (Polynomial.C x₀) =
            (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        rw [hcoeff]
        obtain ⟨c, hc⟩ := leadingCoeff_dvd_evalX_coeff_natDegree hHyp
        rw [hc, map_mul]
        exact ⟨liftToFunctionField (H := H) c, regularElementsSet_liftToFunctionField H c, by
          rw [hWdef]⟩
      obtain ⟨q, hqReg, hqeq⟩ := hWdvd
      -- W-budget: total available `W` power is `(t+2) + (d-2) + 1` (the `+1` from `q`'s `W`).
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) + 1 := by
        rw [hPweq]; omega
      -- rewrite Ddiv with the extra `W` from `coeffReg = W * q`
      rw [hqeq]
      have hreassoc :
          (W * q) * (∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          q * ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2) + 1) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2) + 1) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2) + 1) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show (W * q) * (∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            q * ((∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ ((t + 1 + 1) + (R.natDegree - 2) + 1) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      exact finish_with q _ hqReg hbudget
    · -- non-boundary: the `W`-budget `(t+2)+(d-2)` already covers `Pw = p.2 + j`.
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) := by
        rw [hPweq]
        rw [Finset.mem_range] at hj
        -- `¬(p.2 = t+1 ∧ j = d ∧ 2 ≤ d)`; with `p.2 ≤ t+1`, `j ≤ d`
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · omega
        · -- d ≥ 2:  the negated boundary forces `p.2 ≤ t` or `j ≤ d - 1`
          rcases not_and_or.mp hbdry with h1 | h2
          · -- p.2 ≠ t+1, so p.2 ≤ t
            omega
          · rcases not_and_or.mp h2 with h3 | h4
            · -- j ≠ R.natDegree, so j ≤ d - 1
              omega
            · exact absurd hd h4
      -- rewrite Ddiv directly
      have hreassoc :
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2)) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2)) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2)) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            (shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
              ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ ((t + 1 + 1) + (R.natDegree - 2)) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      exact finish_with _ _ hcoeffReg hbudget

/-- The finite cleared residual is regular once all previous coefficients have
the numerator shape. -/
theorem finiteHenselClearedResidual_regular
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H) (αtrunc : ℕ → 𝕃 H)
    (hshape : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
          (Wfield (H := H) ^ (i + 1) *
            etaField (R := R) (H := H) x₀ hHyp ^
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)
      else 0) :
    (ProximityPrize.SubmissionLower.FiniteHensel.residual
      (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) αtrunc t).coeff (t + 1) *
      (Wfield (H := H) ^ (t + 1 + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
        Wfield (H := H) ^ (R.natDegree - 2)) ∈ regularElementsSet H := by
  classical
  unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
  rw [Polynomial.eval₂_eq_sum_range]
  have hcoeff :
      (∑ i ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
          (fieldTo𝕃 (H := H) x₀) ((liftedR (R := R) (H := H)).coeff i) *
          ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t ^ i).coeff (t + 1) =
      ∑ i ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        (ProximityPrize.SubmissionLower.FiniteHensel.shiftMap
          (fieldTo𝕃 (H := H) x₀) ((liftedR (R := R) (H := H)).coeff i) *
          ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t ^ i).coeff (t + 1) := by
    simp
  rw [hcoeff, Finset.sum_mul]
  apply regularElementsSet_sum
  intro j hjlift
  have hj : j ∈ Finset.range (R.natDegree + 1) := by
    rw [Finset.mem_range] at hjlift ⊢
    have hmap : (liftedR (R := R) (H := H)).natDegree ≤ R.natDegree :=
      Polynomial.natDegree_map_le
    omega
  have hcoeffmap : (liftedR (R := R) (H := H)).coeff j =
      (R.coeff j).map (liftToFunctionField (H := H)) := by
    simp [liftedR, Polynomial.coeff_map]
  rw [hcoeffmap]
  change ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) *
      (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries αtrunc t) ^ j).coeff (t + 1) *
      (Wfield (H := H) ^ (t + 1 + 1) *
        etaField (R := R) (H := H) x₀ hHyp ^
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (t + 1) - 1) *
        Wfield (H := H) ^ (R.natDegree - 2))) ∈ regularElementsSet H
  exact finiteHenselClearedTerm_regular x₀ R H hHyp hzeta t βprev αtrunc hshape j hj


/-- Strong-induction regularity of the concrete cleared finite numerators. -/
theorem betaDiagonal_regular
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (N : ℕ) :
    ∀ t, t ≤ N → betaDiagonal (R := R) (H := H) x₀ hHyp N t ∈ regularElementsSet H := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          have hW : Wfield (H := H) ≠ 0 := Wfield_ne_zero (H := H)
          unfold betaDiagonal alphaDiagonal
          simp only [ProximityPrize.SubmissionLower.FiniteHensel.liftPoly,
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_zero,
            pow_zero, mul_one, zero_add, pow_one]
          rw [Polynomial.coeff_C_zero]
          unfold initialValue Wfield
          rw [div_mul_cancel₀ _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))]
          exact regularElementsSet_functionFieldT H
      | succ m =>
          let oldp := ProximityPrize.SubmissionLower.FiniteHensel.liftPoly
            (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
            (initialValue (H := H)) N m
          let old : ℕ → 𝕃 H := fun i => oldp.coeff i
          have hmN : m ≤ N := by omega
          have hdeg : oldp.natDegree ≤ m := liftPoly_natDegree_le (R := R) (H := H) x₀ N m
          have holdzero : ∀ i, m < i → old i = 0 := by
            intro i hi
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hW : Wfield (H := H) ≠ 0 := Wfield_ne_zero (H := H)
          have heta : etaField (R := R) (H := H) x₀ hHyp ≠ 0 := by
            rw [etaField_eq]
            exact mul_ne_zero (pow_ne_zero _ hW) hzeta
          let βprev : Fin (m + 1) → 𝒪 H := fun i =>
            Classical.choose (ih i.val (by omega) (by omega))
          have hβprev (i : Fin (m + 1)) :
              embeddingOf𝒪Into𝕃 H (βprev i) =
                betaDiagonal (R := R) (H := H) x₀ hHyp N i.val := by
            exact (Classical.choose_spec (ih i.val (by omega) (by omega))).symm
          have hshape : ∀ i : ℕ, old i =
              if hle : i ≤ m then
                embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
                  (Wfield (H := H) ^ (i + 1) *
                    etaField (R := R) (H := H) x₀ hHyp ^
                      ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)
              else 0 := by
            intro i
            by_cases hi : i ≤ m
            · rw [dif_pos hi, hβprev]
              have hdiag : old i = alphaDiagonal (R := R) (H := H) x₀ N i :=
                liftPoly_coeff_eq_diagonal (R := R) (H := H) x₀ N m i hi
              rw [hdiag]
              unfold betaDiagonal
              field_simp [hW, heta]
            · rw [dif_neg hi]
              exact holdzero i (by omega)
          have hreg := finiteHenselClearedResidual_regular x₀ R H hHyp hzeta m βprev old hshape
          have htruncN :
              ProximityPrize.SubmissionLower.FiniteHensel.truncSeries old N = oldp :=
            truncSeries_coeff_eq (H := H) oldp N (hdeg.trans hmN)
          have htruncm :
              ProximityPrize.SubmissionLower.FiniteHensel.truncSeries old m = oldp :=
            truncSeries_coeff_eq (H := H) oldp m hdeg
          have herr :
              (ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) =
              (ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old m).coeff (m + 1) := by
            unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
            rw [htruncN, htruncm]
          rw [← herr] at hreg
          have holdtop : old (m + 1) = 0 := holdzero _ (by omega)
          have hnew : alphaDiagonal (R := R) (H := H) x₀ N (m + 1) =
              -((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1)) /
                zeta R x₀ H := by
            have hs := ProximityPrize.SubmissionLower.FiniteHensel.liftPoly_succ_coeff_sub
              (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
              (initialValue (H := H)) N m
            change alphaDiagonal (R := R) (H := H) x₀ N (m + 1) - old (m + 1) = _ at hs
            rw [holdtop, sub_zero, ySlope_liftedR_eq_zeta] at hs
            exact hs
          rw [show betaDiagonal (R := R) (H := H) x₀ hHyp N (m + 1) =
              -((ProximityPrize.SubmissionLower.FiniteHensel.residual
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) *
                (Wfield (H := H) ^ (m + 1 + 1) *
                  etaField (R := R) (H := H) x₀ hHyp ^
                    (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1) *
                  Wfield (H := H) ^ (R.natDegree - 2))) by
            unfold betaDiagonal
            rw [hnew, etaField_eq]
            have hepos : 0 < ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) := by
              rw [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent_succ]
              omega
            rw [show ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) =
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1) + 1 by omega,
              pow_succ]
            field_simp [hzeta]
            rw [show
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1 + 1 - 1 =
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent (m + 1) - 1 by
                omega]
            rw [pow_succ]
            ring]
          exact regularElementsSet_neg hreg


lemma finiteAlpha_eq_alphaDiagonal (x₀ : F) (N t : ℕ) (ht : t ≤ N) :
    finiteAlpha (R := R) (H := H) x₀ N t =
      alphaDiagonal (R := R) (H := H) x₀ N t := by
  unfold finiteAlpha ProximityPrize.SubmissionLower.FiniteHensel.liftCoeff
  exact liftPoly_coeff_eq_diagonal (R := R) (H := H) x₀ N N t ht

lemma betaField_eq_betaDiagonal (x₀ : F) (hHyp : Hypotheses x₀ R H)
    (N t : ℕ) (ht : t ≤ N) :
    betaField (R := R) (H := H) x₀ hHyp N t =
      betaDiagonal (R := R) (H := H) x₀ hHyp N t := by
  unfold betaField betaDiagonal
  rw [finiteAlpha_eq_alphaDiagonal (R := R) (H := H) x₀ N t ht]

/-- Concrete regularity half of Claim A.2 for every finite lift coefficient. -/
theorem betaField_regular
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (N t : ℕ) (ht : t ≤ N) :
    betaField (R := R) (H := H) x₀ hHyp N t ∈ regularElementsSet H := by
  rw [betaField_eq_betaDiagonal (R := R) (H := H) x₀ hHyp N t ht]
  exact betaDiagonal_regular x₀ R H hHyp hzeta N t ht

/-- A canonical regular numerator chosen from the concrete regularity proof. -/
noncomputable def betaRegular
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (N t : ℕ) (ht : t ≤ N) : 𝒪 H :=
  Classical.choose (betaField_regular x₀ R H hHyp hzeta N t ht)

lemma embedding_betaRegular
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (N t : ℕ) (ht : t ≤ N) :
    embeddingOf𝒪Into𝕃 H (betaRegular x₀ R H hHyp hzeta N t ht) =
      betaField (R := R) (H := H) x₀ hHyp N t :=
  (Classical.choose_spec (betaField_regular x₀ R H hHyp hzeta N t ht)).symm


/-- Sharp and loose weight bounds for the canonical concrete numerator. -/
theorem betaRegular_weight_sharp
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N t : ℕ) (ht : t ≤ N) :
    regularWeight hH (betaRegular x₀ R H hHyp hzeta N t ht) D ≤
      (WithBot.some (numeratorShapeSharp R H D t) : WithBot ℕ) := by
  have hw := betaDiagonal_weight_sharp x₀ R H hHyp hzeta hH hD_H hD_R hRdeg N t ht
  rw [← betaField_eq_betaDiagonal (R := R) (H := H) x₀ hHyp N t ht] at hw
  obtain ⟨b, hb, hwb⟩ := hw
  have hemb := embedding_betaRegular x₀ R H hHyp hzeta N t ht
  have heq : betaRegular x₀ R H hHyp hzeta N t ht = b := by
    apply embeddingOf𝒪Into𝕃_injective hH
    rw [hemb, hb]
  rw [heq]
  exact hwb


theorem betaRegular_weight_sharp_yz
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N t : ℕ) (ht : t ≤ N) :
    regularWeight hH (betaRegular x₀ R H hHyp hzeta N t ht) D ≤
      (WithBot.some (numeratorShapeSharp R H D t) : WithBot ℕ) := by
  have hw := betaDiagonal_weight_sharp_yz x₀ R H hHyp hzeta hH hD_H hYZ hRdeg N t ht
  rw [← betaField_eq_betaDiagonal (R := R) (H := H) x₀ hHyp N t ht] at hw
  obtain ⟨b, hb, hwb⟩ := hw
  have hemb := embedding_betaRegular x₀ R H hHyp hzeta N t ht
  have heq : betaRegular x₀ R H hHyp hzeta N t ht = b := by
    apply embeddingOf𝒪Into𝕃_injective hH
    rw [hemb, hb]
  rw [heq]
  exact hwb

theorem betaRegular_weight_bound
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N t : ℕ) (ht : t ≤ N) :
    regularWeight hH (betaRegular x₀ R H hHyp hzeta N t ht) D ≤
      (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  exact (betaRegular_weight_sharp x₀ R H hHyp hzeta hH hD_H hD_R hRdeg N t ht).trans
    (by exact_mod_cast numeratorShapeSharp_le_loose x₀ R H hHyp hH hD_H t)


lemma regularWeightLe_fieldToL {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (a : F) :
    RegularWeightLe hH (fieldTo𝕃 (H := H) a) D 0 := by
  change RegularWeightLe hH (liftToFunctionField (H := H) (Polynomial.C a)) D 0
  exact (regularWeightLe_liftToFunctionField hD hH _).mono (by simp)

/-- Common denominator used for one evaluated finite lift. -/
noncomputable def commonDenominator (x₀ : F) (hHyp : Hypotheses x₀ R H) (k : ℕ) : 𝕃 H :=
  Wfield (H := H) ^ (k + 1) *
    etaField (R := R) (H := H) x₀ hHyp ^
      ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k

noncomputable def evaluatedFiniteAlpha (x₀ x : F) (N k : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range (k + 1),
    finiteAlpha (R := R) (H := H) x₀ N i * fieldTo𝕃 (H := H) x ^ i

lemma evaluatedFiniteAlpha_eq_eval (x₀ x : F) (N k : ℕ) :
    evaluatedFiniteAlpha (R := R) (H := H) x₀ x N k =
      (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries
        (finiteAlpha (R := R) (H := H) x₀ N) k).eval (fieldTo𝕃 (H := H) x) := by
  unfold evaluatedFiniteAlpha ProximityPrize.SubmissionLower.FiniteHensel.truncSeries
  change (∑ i ∈ Finset.range (k + 1), _ ) =
    (Polynomial.evalRingHom (fieldTo𝕃 (H := H) x)) (∑ i ∈ Finset.range (k + 1), _)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- The field element whose regular numerator records failure of the evaluated
lift to equal an affine function of the function-field variable. -/
noncomputable def gammaDifferenceField (x₀ x u₀ u₁ : F)
    (hHyp : Hypotheses x₀ R H) (N k : ℕ) : 𝕃 H :=
  (evaluatedFiniteAlpha (R := R) (H := H) x₀ x N k -
      (fieldTo𝕃 (H := H) u₀ + functionFieldT (H := H) * fieldTo𝕃 (H := H) u₁)) *
    commonDenominator (R := R) (H := H) x₀ hHyp k

lemma denominatorExponent_mono {i k : ℕ} (hik : i ≤ k) :
    ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i ≤
      ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k := by
  simp [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent]
  omega

lemma regularWeightLe_functionFieldT {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) :
    RegularWeightLe hH (functionFieldT (H := H)) D
      (D - Bivariate.natDegreeY H + 1) := by
  refine ⟨(Ideal.Quotient.mk (Ideal.span {monicize H})
    (Polynomial.X : F[X][Y]) : 𝒪 H), ?_, ?_⟩
  · rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]
  · refine (regularWeight_mk_le hD hH (Polynomial.X : F[X][Y])).trans ?_
    have hX : weight (Polynomial.X : F[X][Y]) H D ≤
        (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
      simpa only [pow_one, one_mul] using (weight_X_pow_le (H := H) (D := D) (k := 1))
    exact hX.trans (by exact_mod_cast (show D + 1 - Bivariate.natDegreeY H ≤ D - Bivariate.natDegreeY H + 1 by omega))

/-- Weight certificate for the per-coordinate common-denominator difference. -/
theorem gammaDifference_weight
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    RegularWeightLe hH (gammaDifferenceField (R := R) (H := H)
      x₀ x u₀ u₁ hHyp N k) D
      ((2 * k + 1) * Bivariate.natDegreeY R * D) := by
  classical
  let W := Wfield (H := H)
  let eta := etaField (R := R) (H := H) x₀ hHyp
  let ΛW := D - Bivariate.natDegreeY H
  let Λξ := (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
  let B := (2 * k + 1) * Bivariate.natDegreeY R * D
  have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) :=
    evalX_totalDegree_le_of_coeff_bound_finite x₀ R hD_R
  have hWc : RegularWeightLe hH W D ΛW := by
    exact regularWeightLe_leadingCoeff_sharp hD_H hH
  have hetac : RegularWeightLe hH eta D Λξ := by
    refine ⟨xi x₀ R H hHyp, rfl, ?_⟩
    exact xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hx : RegularWeightLe hH (fieldTo𝕃 (H := H) x) D 0 :=
    regularWeightLe_fieldToL hD_H hH x
  have hsum : RegularWeightLe hH
      (evaluatedFiniteAlpha (R := R) (H := H) x₀ x N k *
        commonDenominator (R := R) (H := H) x₀ hHyp k) D B := by
    unfold evaluatedFiniteAlpha commonDenominator
    rw [Finset.sum_mul]
    refine RegularWeightLe.sum _ _ hD_H ?_
    intro i hi
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hiN : i ≤ N := hik.trans hkN
    have hb := betaDiagonal_weight_sharp x₀ R H hHyp hzeta hH hD_H hD_R hRdeg N i hiN
    rw [← betaField_eq_betaDiagonal (R := R) (H := H) x₀ hHyp N i hiN] at hb
    have hemono := denominatorExponent_mono hik
    have hterm :
        (finiteAlpha (R := R) (H := H) x₀ N i * fieldTo𝕃 (H := H) x ^ i) *
            (W ^ (k + 1) * eta ^
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k) =
          betaField (R := R) (H := H) x₀ hHyp N i * fieldTo𝕃 (H := H) x ^ i *
            (W ^ (k - i) * eta ^
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
                ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)) := by
      unfold betaField W eta
      have hw : k + 1 = (i + 1) + (k - i) := by omega
      have he : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k =
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i +
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) := by omega
      rw [hw, he, pow_add, pow_add]
      rw [Nat.add_sub_cancel_left]
      ring
    rw [hterm]
    refine (RegularWeightLe.mul hD_H
      (RegularWeightLe.mul hD_H hb (hx.pow hD_H i))
      (RegularWeightLe.mul hD_H (hWc.pow hD_H (k - i))
        (hetac.pow hD_H
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)))).mono ?_
    dsimp [B, ΛW, Λξ]
    have hs := numeratorShapeSharp_le_loose x₀ R H hHyp hH hD_H k
    have htelescope : numeratorShapeSharp R H D i +
          ((k - i) * (D - Bivariate.natDegreeY H) +
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) *
              ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) ≤
        numeratorShapeSharp R H D k := by
      unfold numeratorShapeSharp
      have hcorr : (i - 1) * (D - Bivariate.natDegreeY R) ≤
          (k - 1) * (D - Bivariate.natDegreeY R) :=
        Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hik 1)
      have hwadd : (i + 1) + (k - i) = k + 1 := by omega
      have headd : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i +
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) =
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k := by omega
      calc
        _ = 1 + ((i + 1) + (k - i)) * (D - Bivariate.natDegreeY H) +
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i +
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
                ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)) *
              ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) +
            (i - 1) * (D - Bivariate.natDegreeY R) := by ring
        _ = 1 + (k + 1) * (D - Bivariate.natDegreeY H) +
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k *
              ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) +
            (i - 1) * (D - Bivariate.natDegreeY R) := by rw [hwadd, headd]
        _ ≤ _ := Nat.add_le_add_left hcorr _
    exact htelescope.trans hs
  have haff : RegularWeightLe hH
      ((fieldTo𝕃 (H := H) u₀ + functionFieldT (H := H) * fieldTo𝕃 (H := H) u₁) *
        commonDenominator (R := R) (H := H) x₀ hHyp k) D B := by
    have hu0 := regularWeightLe_fieldToL hD_H hH u₀
    have hu1 := regularWeightLe_fieldToL hD_H hH u₁
    have hT := regularWeightLe_functionFieldT (H := H) hD_H hH
    have hden := RegularWeightLe.mul hD_H (hWc.pow hD_H (k + 1))
      (hetac.pow hD_H
        (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k))
    unfold commonDenominator
    refine (RegularWeightLe.mul hD_H
      (RegularWeightLe.add hD_H (hu0.mono (by omega))
        (RegularWeightLe.mul hD_H hT hu1))
      hden).mono ?_
    dsimp [B, ΛW, Λξ]
    have hdHle : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
      natDegree_H_le_natDegree_R_of_hypotheses hHyp
    have hdHpos : 1 ≤ Bivariate.natDegreeY H := hH
    have hdHD : Bivariate.natDegreeY H ≤ D := by
      have hHin : H.natDegree ∈ H.support :=
        Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hH))
      have hcoef := Bivariate.coeff_totalDegree_le H hHin
      rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
      omega
    have hek : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k ≤ 2 * k := by
      simp [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent]
    set dh := Bivariate.natDegreeY H
    set dy := Bivariate.natDegreeY R
    obtain ⟨a, ha⟩ : ∃ a, D = dh + a := ⟨D - dh, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, dy = dh + b := ⟨dy - dh, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, dh = c + 1 := ⟨dh - 1, by omega⟩
    rw [ha, hb, hc]
    simp only [Nat.add_sub_cancel_left]
    have hecost : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k *
          ((c + 1 + b - 1) * (a + 1)) ≤
        2 * k * ((c + b) * (a + 1)) := by
      rw [show c + 1 + b - 1 = c + b by omega]
      exact Nat.mul_le_mul_right _ hek
    calc
      a + 1 + ((k + 1) * a +
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k *
            ((c + 1 + b - 1) * (a + 1)))
        ≤ a + 1 + ((k + 1) * a + 2 * k * ((c + b) * (a + 1))) := by omega
      _ ≤ (2 * k + 1) * (c + 1 + b) * (c + 1 + a) := by
        let LL := a + 1 + ((k + 1) * a + 2 * k * ((c + b) * (a + 1)))
        let RR := (2 * k + 1) * (c + 1 + b) * (c + 1 + a)
        change LL ≤ RR
        by_cases hk0 : k = 0
        · subst k
          have hcb : 1 ≤ c + b := by omega
          obtain ⟨r, hr⟩ : ∃ r, c + b = r + 1 := ⟨c + b - 1, by omega⟩
          have hid : RR = LL + (r * (a + 1) + 1 + c * (c + b + 1)) := by
            dsimp [LL, RR]
            rw [show c + 1 + b = (c + b) + 1 by omega, hr]
            ring
          rw [hid]
          exact Nat.le_add_right _ _
        · obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
          have hid : RR = LL +
              ((c + b) * (a + 1) + q * a + 2 * (q + 1) +
                (2 * (q + 1) + 1) * c * (c + b + 1)) := by
            dsimp [LL, RR]
            ring
          rw [hid]
          exact Nat.le_add_right _ _
  unfold gammaDifferenceField
  rw [sub_mul]
  exact RegularWeightLe.add hD_H hsum (RegularWeightLe.neg haff)


/-- Canonical regular numerator for the per-coordinate gamma difference. -/

theorem gammaDifference_weight_yz
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    RegularWeightLe hH (gammaDifferenceField (R := R) (H := H)
      x₀ x u₀ u₁ hHyp N k) D
      ((2 * k + 1) * Bivariate.natDegreeY R * D) := by
  classical
  let W := Wfield (H := H)
  let eta := etaField (R := R) (H := H) x₀ hHyp
  let ΛW := D - Bivariate.natDegreeY H
  let Λξ := (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
  let B := (2 * k + 1) * Bivariate.natDegreeY R * D
  have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) :=
    evalX_totalDegree_le_of_yzCap x₀ R hYZ
  have hWc : RegularWeightLe hH W D ΛW := by
    exact regularWeightLe_leadingCoeff_sharp hD_H hH
  have hetac : RegularWeightLe hH eta D Λξ := by
    refine ⟨xi x₀ R H hHyp, rfl, ?_⟩
    exact xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hx : RegularWeightLe hH (fieldTo𝕃 (H := H) x) D 0 :=
    regularWeightLe_fieldToL hD_H hH x
  have hsum : RegularWeightLe hH
      (evaluatedFiniteAlpha (R := R) (H := H) x₀ x N k *
        commonDenominator (R := R) (H := H) x₀ hHyp k) D B := by
    unfold evaluatedFiniteAlpha commonDenominator
    rw [Finset.sum_mul]
    refine RegularWeightLe.sum _ _ hD_H ?_
    intro i hi
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hiN : i ≤ N := hik.trans hkN
    have hb := betaDiagonal_weight_sharp_yz x₀ R H hHyp hzeta hH hD_H hYZ hRdeg N i hiN
    rw [← betaField_eq_betaDiagonal (R := R) (H := H) x₀ hHyp N i hiN] at hb
    have hemono := denominatorExponent_mono hik
    have hterm :
        (finiteAlpha (R := R) (H := H) x₀ N i * fieldTo𝕃 (H := H) x ^ i) *
            (W ^ (k + 1) * eta ^
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k) =
          betaField (R := R) (H := H) x₀ hHyp N i * fieldTo𝕃 (H := H) x ^ i *
            (W ^ (k - i) * eta ^
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
                ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)) := by
      unfold betaField W eta
      have hw : k + 1 = (i + 1) + (k - i) := by omega
      have he : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k =
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i +
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) := by omega
      rw [hw, he, pow_add, pow_add]
      rw [Nat.add_sub_cancel_left]
      ring
    rw [hterm]
    refine (RegularWeightLe.mul hD_H
      (RegularWeightLe.mul hD_H hb (hx.pow hD_H i))
      (RegularWeightLe.mul hD_H (hWc.pow hD_H (k - i))
        (hetac.pow hD_H
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)))).mono ?_
    dsimp [B, ΛW, Λξ]
    have hs := numeratorShapeSharp_le_loose x₀ R H hHyp hH hD_H k
    have htelescope : numeratorShapeSharp R H D i +
          ((k - i) * (D - Bivariate.natDegreeY H) +
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
              ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) *
              ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) ≤
        numeratorShapeSharp R H D k := by
      unfold numeratorShapeSharp
      have hcorr : (i - 1) * (D - Bivariate.natDegreeY R) ≤
          (k - 1) * (D - Bivariate.natDegreeY R) :=
        Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hik 1)
      have hwadd : (i + 1) + (k - i) = k + 1 := by omega
      have headd : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i +
          (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i) =
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k := by omega
      calc
        _ = 1 + ((i + 1) + (k - i)) * (D - Bivariate.natDegreeY H) +
            (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i +
              (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k -
                ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent i)) *
              ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) +
            (i - 1) * (D - Bivariate.natDegreeY R) := by ring
        _ = 1 + (k + 1) * (D - Bivariate.natDegreeY H) +
            ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k *
              ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) +
            (i - 1) * (D - Bivariate.natDegreeY R) := by rw [hwadd, headd]
        _ ≤ _ := Nat.add_le_add_left hcorr _
    exact htelescope.trans hs
  have haff : RegularWeightLe hH
      ((fieldTo𝕃 (H := H) u₀ + functionFieldT (H := H) * fieldTo𝕃 (H := H) u₁) *
        commonDenominator (R := R) (H := H) x₀ hHyp k) D B := by
    have hu0 := regularWeightLe_fieldToL hD_H hH u₀
    have hu1 := regularWeightLe_fieldToL hD_H hH u₁
    have hT := regularWeightLe_functionFieldT (H := H) hD_H hH
    have hden := RegularWeightLe.mul hD_H (hWc.pow hD_H (k + 1))
      (hetac.pow hD_H
        (ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k))
    unfold commonDenominator
    refine (RegularWeightLe.mul hD_H
      (RegularWeightLe.add hD_H (hu0.mono (by omega))
        (RegularWeightLe.mul hD_H hT hu1))
      hden).mono ?_
    dsimp [B, ΛW, Λξ]
    have hdHle : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
      natDegree_H_le_natDegree_R_of_hypotheses hHyp
    have hdHpos : 1 ≤ Bivariate.natDegreeY H := hH
    have hdHD : Bivariate.natDegreeY H ≤ D := by
      have hHin : H.natDegree ∈ H.support :=
        Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hH))
      have hcoef := Bivariate.coeff_totalDegree_le H hHin
      rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
      omega
    have hek : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k ≤ 2 * k := by
      simp [ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent]
    set dh := Bivariate.natDegreeY H
    set dy := Bivariate.natDegreeY R
    obtain ⟨a, ha⟩ : ∃ a, D = dh + a := ⟨D - dh, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, dy = dh + b := ⟨dy - dh, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, dh = c + 1 := ⟨dh - 1, by omega⟩
    rw [ha, hb, hc]
    simp only [Nat.add_sub_cancel_left]
    have hecost : ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k *
          ((c + 1 + b - 1) * (a + 1)) ≤
        2 * k * ((c + b) * (a + 1)) := by
      rw [show c + 1 + b - 1 = c + b by omega]
      exact Nat.mul_le_mul_right _ hek
    calc
      a + 1 + ((k + 1) * a +
          ProximityPrize.SubmissionLower.FiniteHenselWeight.denominatorExponent k *
            ((c + 1 + b - 1) * (a + 1)))
        ≤ a + 1 + ((k + 1) * a + 2 * k * ((c + b) * (a + 1))) := by omega
      _ ≤ (2 * k + 1) * (c + 1 + b) * (c + 1 + a) := by
        let LL := a + 1 + ((k + 1) * a + 2 * k * ((c + b) * (a + 1)))
        let RR := (2 * k + 1) * (c + 1 + b) * (c + 1 + a)
        change LL ≤ RR
        by_cases hk0 : k = 0
        · subst k
          have hcb : 1 ≤ c + b := by omega
          obtain ⟨r, hr⟩ : ∃ r, c + b = r + 1 := ⟨c + b - 1, by omega⟩
          have hid : RR = LL + (r * (a + 1) + 1 + c * (c + b + 1)) := by
            dsimp [LL, RR]
            rw [show c + 1 + b = (c + b) + 1 by omega, hr]
            ring
          rw [hid]
          exact Nat.le_add_right _ _
        · obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
          have hid : RR = LL +
              ((c + b) * (a + 1) + q * a + 2 * (q + 1) +
                (2 * (q + 1) + 1) * c * (c + b + 1)) := by
            dsimp [LL, RR]
            ring
          rw [hid]
          exact Nat.le_add_right _ _
  unfold gammaDifferenceField
  rw [sub_mul]
  exact RegularWeightLe.add hD_H hsum (RegularWeightLe.neg haff)


/-- Canonical regular numerator for the per-coordinate gamma difference. -/
noncomputable def gammaDifferenceRegular
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) : 𝒪 H :=
  Classical.choose (gammaDifference_weight x₀ x u₀ u₁ R H hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN)

lemma embedding_gammaDifferenceRegular
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    embeddingOf𝒪Into𝕃 H
      (gammaDifferenceRegular x₀ x u₀ u₁ R H hHyp hzeta hH hD_H hD_R hRdeg N k hkN) =
      gammaDifferenceField (R := R) (H := H) x₀ x u₀ u₁ hHyp N k := by
  exact (Classical.choose_spec (gammaDifference_weight x₀ x u₀ u₁ R H hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN)).1.symm

lemma gammaDifferenceRegular_weight
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH
      (gammaDifferenceRegular x₀ x u₀ u₁ R H hHyp hzeta hH hD_H hD_R hRdeg N k hkN) D ≤
      (WithBot.some ((2 * k + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) :=
  (Classical.choose_spec (gammaDifference_weight x₀ x u₀ u₁ R H hHyp hzeta hH
    hD_H hD_R hRdeg N k hkN)).2


noncomputable def gammaDifferenceRegular_yz
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) : 𝒪 H :=
  Classical.choose (gammaDifference_weight_yz x₀ x u₀ u₁ R H hHyp hzeta hH
    hD_H hYZ hRdeg N k hkN)

lemma embedding_gammaDifferenceRegular_yz
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    embeddingOf𝒪Into𝕃 H
      (gammaDifferenceRegular_yz x₀ x u₀ u₁ R H hHyp hzeta hH hD_H hYZ hRdeg N k hkN) =
      gammaDifferenceField (R := R) (H := H) x₀ x u₀ u₁ hHyp N k := by
  exact (Classical.choose_spec (gammaDifference_weight_yz x₀ x u₀ u₁ R H hHyp hzeta hH
    hD_H hYZ hRdeg N k hkN)).1.symm

lemma gammaDifferenceRegular_weight_yz
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hYZ : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH
      (gammaDifferenceRegular_yz x₀ x u₀ u₁ R H hHyp hzeta hH hD_H hYZ hRdeg N k hkN) D ≤
      (WithBot.some ((2 * k + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) :=
  (Classical.choose_spec (gammaDifference_weight_yz x₀ x u₀ u₁ R H hHyp hzeta hH
    hD_H hYZ hRdeg N k hkN)).2

/-- Agreement with the affine value kills the common-denominator numerator. -/
lemma embedding_gammaDifferenceRegular_eq_zero_of_agreement
    (x₀ x u₀ u₁ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hzeta : zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N)
    (hagree : evaluatedFiniteAlpha (R := R) (H := H) x₀ x N k =
      fieldTo𝕃 (H := H) u₀ + functionFieldT (H := H) * fieldTo𝕃 (H := H) u₁) :
    embeddingOf𝒪Into𝕃 H
      (gammaDifferenceRegular x₀ x u₀ u₁ R H hHyp hzeta hH hD_H hD_R hRdeg N k hkN) = 0 := by
  rw [embedding_gammaDifferenceRegular]
  unfold gammaDifferenceField
  rw [hagree, sub_self, zero_mul]


end
end ConcreteFiniteNumerators
end HenselNumerators
end RationalFunctions

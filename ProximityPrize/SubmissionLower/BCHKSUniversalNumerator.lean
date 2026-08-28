import ProximityPrize.SubmissionLower.BCHKSHenselWeight
import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap
import ProximityPrize.SubmissionLower.BCHKSFiniteHensel


open Polynomial

namespace ProximityPrize.SubmissionLower.UniversalNumerator

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

theorem coeff_finset_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → A[X]) (n : ℕ) :
    (∑ i ∈ S, f i).coeff n = ∑ i ∈ S, (f i).coeff n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

/-- The polynomial whose positive-degree coefficients are the already constructed
universal numerators `N₁, …, Nₙ₋₁`.  The constant coefficient is deliberately
zero: the symbolic root coordinate is handled by shifting the Y variable first. -/
def positivePrefix (prior : ℕ → A) (n : ℕ) : A[X] :=
  ∑ i ∈ Finset.range n, if i = 0 then 0 else
    Polynomial.monomial i (prior i)

@[simp] theorem positivePrefix_zero (prior : ℕ → A) :
    positivePrefix prior 0 = 0 := by
  simp [positivePrefix]

theorem positivePrefix_coeff (prior : ℕ → A) (n i : ℕ) :
    (positivePrefix prior n).coeff i = if 0 < i ∧ i < n then prior i else 0 := by
  classical
  rw [positivePrefix, coeff_finset_sum]
  by_cases hi0 : i = 0
  · subst i
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hb0 : b = 0
    · simp [hb0]
    · simp only [hb0, if_false, coeff_monomial]
  by_cases hin : i < n
  · have himem : i ∈ Finset.range n := by simpa using hin
    rw [Finset.sum_eq_single i]
    · simp [hi0, hin]
    · intro b hb hbi
      by_cases hb0 : b = 0
      · simp [hb0]
      · simp only [hb0, if_false, coeff_monomial]
        rw [if_neg hbi]
    · intro hnot
      exact (hnot himem).elim
  · have himem : i ∉ Finset.range n := by simpa using hin
    have hsum : (∑ b ∈ Finset.range n,
        (if b = 0 then (0 : A[X]) else Polynomial.monomial b (prior b)).coeff i) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hb0 : b = 0
      · simp [hb0]
      · simp only [hb0, if_false, coeff_monomial]
        rw [if_neg]
        intro hbi
        subst b
        exact himem hb
    rw [hsum]
    simp [hin]

theorem positivePrefix_coeff_self (prior : ℕ → A) (n : ℕ) :
    (positivePrefix prior n).coeff n = 0 := by
  rw [positivePrefix_coeff]
  simp

/-- One summand in the branch-independent numerator recurrence.  Here `Rshift`
is `R(x₀+U,Y+V,Z)`, represented as a polynomial in `V` whose coefficients are
polynomials in `U` over the coefficient ring `A = F[Z,Y]`.

For a term `U^a V^b`, the denominator padding is exactly `2a+b-2`; this is
independent of the composition of `n-a` among the `b` prior coefficients. -/
def residualTerm (Rshift : A[X][X]) (s : A) (n a b : ℕ)
    (prior : ℕ → A) : A :=
  ((Rshift.coeff b).coeff a) * s ^ (2 * a + b - 2) *
    ((positivePrefix prior n) ^ b).coeff (n - a)

/-- Cleared coefficient recurrence for the `n`-th implicit Taylor numerator.
It is intended for `n ≥ 1`.  Terms outside the displayed finite ranges vanish. -/
def numeratorStep (Rshift : A[X][X]) (s : A) (d n : ℕ)
    (prior : ℕ → A) : A :=
  -∑ a ∈ Finset.range (n + 1),
    ∑ b ∈ Finset.range (d + 1), residualTerm Rshift s n a b prior

/-- The universal numerator sequence.  Index zero is unused and set to zero;
successor indices are defined course-of-values through `betaSequenceFull`. -/
def numerators (Rshift : A[X][X]) (s : A) (d : ℕ) : ℕ → A :=
  ProximityPrize.SubmissionLower.FiniteHenselWeight.betaSequenceFull 0
    (fun t prior => numeratorStep Rshift s d (t + 1) prior)

@[simp] theorem numerators_zero (Rshift : A[X][X]) (s : A) (d : ℕ) :
    numerators Rshift s d 0 = 0 := by
  simp [numerators, ProximityPrize.SubmissionLower.FiniteHenselWeight.betaSequenceFull]

@[simp] theorem numerators_succ (Rshift : A[X][X]) (s : A) (d t : ℕ) :
    numerators Rshift s d (t + 1) = numeratorStep Rshift s d (t + 1)
      (fun i => if i ≤ t then numerators Rshift s d i else 0) := by
  simp [numerators, ProximityPrize.SubmissionLower.FiniteHenselWeight.betaSequenceFull]

theorem positivePrefix_map (f : A →+* B) (prior : ℕ → A) (n : ℕ) :
    (positivePrefix prior n).map f = positivePrefix (fun i => f (prior i)) n := by
  classical
  simp only [positivePrefix, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split
  · simp
  · simp

theorem residualTerm_map (f : A →+* B) (Rshift : A[X][X]) (s : A)
    (n a b : ℕ) (prior : ℕ → A) :
    f (residualTerm Rshift s n a b prior) =
      residualTerm (Rshift.map (mapRingHom f)) (f s) n a b (fun i => f (prior i)) := by
  classical
  have hRcoeff : f ((Rshift.coeff b).coeff a) =
      ((Rshift.map (mapRingHom f)).coeff b).coeff a := by simp
  have hPcoeff : f (((positivePrefix prior n) ^ b).coeff (n - a)) =
      ((positivePrefix (fun i => f (prior i)) n) ^ b).coeff (n - a) := by
    rw [← coeff_map, Polynomial.map_pow, positivePrefix_map]
  simp only [residualTerm, map_mul, map_pow, hRcoeff, hPcoeff]

theorem numeratorStep_map (f : A →+* B) (Rshift : A[X][X]) (s : A)
    (d n : ℕ) (prior : ℕ → A) :
    f (numeratorStep Rshift s d n prior) =
      numeratorStep (Rshift.map (mapRingHom f)) (f s) d n (fun i => f (prior i)) := by
  classical
  simp only [numeratorStep, map_neg, map_sum, residualTerm_map]

theorem numerators_map (f : A →+* B) (Rshift : A[X][X]) (s : A) (d : ℕ) :
    ∀ n, f (numerators Rshift s d n) =
      numerators (Rshift.map (mapRingHom f)) (f s) d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ t =>
          rw [numerators_succ, numerators_succ, numeratorStep_map]
          congr 2
          funext i
          by_cases hi : i ≤ t
          · simp only [hi, if_true]
            exact ih i (by omega)
          · simp [hi]

end

end ProximityPrize.SubmissionLower.UniversalNumerator

open Polynomial

namespace ProximityPrize.SubmissionLower.UniversalNumerator

noncomputable section

variable {F : Type*} [CommRing F]

theorem natDegree_finset_prod_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → F[X]) :
    (∏ i ∈ S, f i).natDegree ≤ ∑ i ∈ S, (f i).natDegree := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left ih _)

theorem degreeX_finset_prod_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → F[X][X]) :
    Bivariate.degreeX (∏ i ∈ S, f i) ≤ ∑ i ∈ S, Bivariate.degreeX (f i) := by
  induction S using Finset.induction_on with
  | empty =>
      unfold Bivariate.degreeX
      apply Finset.sup_le
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simp
      · have hz : (1 : F[X][X]).coeff i = 0 := by
          rw [Polynomial.coeff_one, if_neg hi0]
        exact (Polynomial.mem_support_iff.mp hi hz).elim
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (Bivariate.degreeX_mul_le _ _).trans (Nat.add_le_add_left ih _)

theorem degreeX_neg (p : F[X][X]) :
    Bivariate.degreeX (-p) = Bivariate.degreeX p := by
  classical
  unfold Bivariate.degreeX
  rw [Polynomial.support_neg]
  apply Finset.sup_congr rfl
  intro i hi
  rw [Polynomial.coeff_neg, Polynomial.natDegree_neg]

theorem degreeX_pow_le (p : F[X][X]) (m : ℕ) :
    Bivariate.degreeX (p ^ m) ≤ m * Bivariate.degreeX p := by
  induction m with
  | zero =>
      rw [pow_zero, Nat.zero_mul]
      unfold Bivariate.degreeX
      apply Finset.sup_le
      intro i hi
      by_cases hi0 : i = 0
      · subst i; simp
      · have hz : (1 : F[X][X]).coeff i = 0 := by
          rw [Polynomial.coeff_one, if_neg hi0]
        exact (Polynomial.mem_support_iff.mp hi hz).elim
  | succ m ih =>
      rw [pow_succ, Nat.succ_mul]
      exact (Bivariate.degreeX_mul_le _ _).trans (Nat.add_le_add_right ih _)

theorem positivePrefix_pow_coeff_eq_zero_of_lt {A : Type*} [CommRing A]
    (c : ℕ → A) (n b q : ℕ) (hq : q < b) :
    ((positivePrefix c n) ^ b).coeff q = 0 := by
  have hx : (Polynomial.X : A[X]) ∣ positivePrefix c n := by
    rw [Polynomial.X_dvd_iff, positivePrefix_coeff]
    simp
  have hdvd : (Polynomial.X : A[X]) ^ b ∣ (positivePrefix c n) ^ b :=
    pow_dvd_pow_of_dvd hx b
  exact Polynomial.X_pow_dvd_iff.mp hdvd q hq

private theorem denominator_mass_sum {b q : ℕ} (l : ℕ →₀ ℕ)
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range b) q)
    (hpos : ∀ i ∈ Finset.range b, 0 < l i) :
    (∑ i ∈ Finset.range b, (2 * l i - 1)) = 2 * q - b := by
  rw [Finset.mem_finsuppAntidiag] at hl
  have hsum : (∑ i ∈ Finset.range b, l i) = q := hl.1
  have hdouble : (∑ i ∈ Finset.range b, 2 * l i) = 2 * q := by
    rw [← Finset.mul_sum, hsum]
  have hadd : (∑ i ∈ Finset.range b, (2 * l i - 1)) + b =
      ∑ i ∈ Finset.range b, 2 * l i := by
    calc
      (∑ i ∈ Finset.range b, (2 * l i - 1)) + b =
          (∑ i ∈ Finset.range b, (2 * l i - 1)) +
            ∑ _i ∈ Finset.range b, 1 := by simp
      _ = ∑ i ∈ Finset.range b, ((2 * l i - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ Finset.range b, 2 * l i := by
        apply Finset.sum_congr rfl
        intro i hi
        have := hpos i hi
        omega
  omega

theorem positivePrefix_pow_coeff_natDegree_le
    (prior : ℕ → F[X]) (n b q d : ℕ)
    (hprior : ∀ i, 0 < i → i < n →
      (prior i).natDegree ≤ (2 * i - 1) * d) :
    (((positivePrefix prior n) ^ b).coeff q).natDegree ≤ (2 * q - b) * d := by
  classical
  rw [RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.polynomial_coeff_pow]
  apply YZFactorCap.natDegree_sum_le_of_forall
  intro l hl
  by_cases hz : ∃ i ∈ Finset.range b, l i = 0
  · obtain ⟨i, hi, hli⟩ := hz
    have hprod : (∏ j ∈ Finset.range b, (positivePrefix prior n).coeff (l j)) = 0 := by
      apply Finset.prod_eq_zero hi
      rw [hli, positivePrefix_coeff]
      simp
    rw [hprod]
    simp
  · push_neg at hz
    have hlmem := hl
    rw [Finset.mem_finsuppAntidiag] at hlmem
    have hli_lt : ∀ i ∈ Finset.range b, l i < n ∨
        (positivePrefix prior n).coeff (l i) = 0 := by
      intro i hi
      by_cases h : l i < n
      · exact Or.inl h
      · right
        rw [positivePrefix_coeff]
        simp [h]
    by_cases hzero : ∃ i ∈ Finset.range b,
        (positivePrefix prior n).coeff (l i) = 0
    · obtain ⟨i, hi, hzi⟩ := hzero
      rw [Finset.prod_eq_zero hi hzi]
      simp
    · push_neg at hzero
      have hlt : ∀ i ∈ Finset.range b, l i < n := by
        intro i hi
        exact (hli_lt i hi).resolve_right (hzero i hi)
      have hcoeff : ∀ i ∈ Finset.range b,
          (positivePrefix prior n).coeff (l i) = prior (l i) := by
        intro i hi
        rw [positivePrefix_coeff,
          if_pos ⟨Nat.pos_of_ne_zero (hz i hi), hlt i hi⟩]
      rw [Finset.prod_congr rfl hcoeff]
      calc
        (∏ i ∈ Finset.range b, prior (l i)).natDegree
            ≤ ∑ i ∈ Finset.range b, (prior (l i)).natDegree :=
          natDegree_finset_prod_le _ _
        _ ≤ ∑ i ∈ Finset.range b, (2 * l i - 1) * d := by
          exact Finset.sum_le_sum fun i hi =>
            hprior (l i) (Nat.pos_of_ne_zero (hz i hi)) (hlt i hi)
        _ = (2 * q - b) * d := by
          rw [← Finset.sum_mul,
            denominator_mass_sum l hl (fun i hi => Nat.pos_of_ne_zero (hz i hi))]

theorem positivePrefix_pow_coeff_degreeX_le
    (prior : ℕ → F[X][X]) (n b q D : ℕ)
    (hprior : ∀ i, 0 < i → i < n →
      Bivariate.degreeX (prior i) ≤ (2 * i - 1) * D) :
    Bivariate.degreeX (((positivePrefix prior n) ^ b).coeff q) ≤ (2 * q - b) * D := by
  classical
  rw [RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.polynomial_coeff_pow]
  apply YZFactorCap.degreeX_sum_le_of_forall
  intro l hl
  by_cases hz : ∃ i ∈ Finset.range b, l i = 0
  · obtain ⟨i, hi, hli⟩ := hz
    have hprod : (∏ j ∈ Finset.range b, (positivePrefix prior n).coeff (l j)) = 0 := by
      apply Finset.prod_eq_zero hi
      rw [hli, positivePrefix_coeff]
      simp
    rw [hprod]
    simp [Bivariate.degreeX]
  · push_neg at hz
    have hlmem := hl
    rw [Finset.mem_finsuppAntidiag] at hlmem
    by_cases hzero : ∃ i ∈ Finset.range b,
        (positivePrefix prior n).coeff (l i) = 0
    · obtain ⟨i, hi, hzi⟩ := hzero
      rw [Finset.prod_eq_zero hi hzi]
      simp [Bivariate.degreeX]
    · push_neg at hzero
      have hlt : ∀ i ∈ Finset.range b, l i < n := by
        intro i hi
        by_contra h
        have hzcoeff : (positivePrefix prior n).coeff (l i) = 0 := by
          rw [positivePrefix_coeff]
          simp [h]
        exact hzero i hi hzcoeff
      have hcoeff : ∀ i ∈ Finset.range b,
          (positivePrefix prior n).coeff (l i) = prior (l i) := by
        intro i hi
        rw [positivePrefix_coeff,
          if_pos ⟨Nat.pos_of_ne_zero (hz i hi), hlt i hi⟩]
      rw [Finset.prod_congr rfl hcoeff]
      calc
        Bivariate.degreeX (∏ i ∈ Finset.range b, prior (l i))
            ≤ ∑ i ∈ Finset.range b, Bivariate.degreeX (prior (l i)) :=
          degreeX_finset_prod_le _ _
        _ ≤ ∑ i ∈ Finset.range b, (2 * l i - 1) * D := by
          exact Finset.sum_le_sum fun i hi =>
            hprior (l i) (Nat.pos_of_ne_zero (hz i hi)) (hlt i hi)
        _ = (2 * q - b) * D := by
          rw [← Finset.sum_mul,
            denominator_mass_sum l hl (fun i hi => Nat.pos_of_ne_zero (hz i hi))]

theorem residualTerm_natDegree_le
    (Rshift : F[X][X][X]) (s : F[X]) (n a b d : ℕ)
    (hn : 0 < n) (ha : a ≤ n) (hd : 0 < d)
    (hcoeff : ((Rshift.coeff b).coeff a).natDegree ≤ d)
    (hs : s.natDegree ≤ d - 1)
    (prior : ℕ → F[X])
    (hprior : ∀ i, 0 < i → i < n →
      (prior i).natDegree ≤ (2 * i - 1) * d) :
    (residualTerm Rshift s n a b prior).natDegree ≤ (2 * n - 1) * d := by
  by_cases hsmall : 2 * a + b < 2
  · have ha0 : a = 0 := by omega
    subst a
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    · have hcoeffzero : ((positivePrefix prior n) ^ 0).coeff (n - 0) = 0 := by
        rw [pow_zero, Nat.sub_zero, Polynomial.coeff_one, if_neg hn.ne']
      unfold residualTerm
      rw [hcoeffzero, mul_zero]
      simp
    · have hcoeffzero : ((positivePrefix prior n) ^ 1).coeff (n - 0) = 0 := by
        rw [pow_one, Nat.sub_zero, positivePrefix_coeff_self]
      unfold residualTerm
      rw [hcoeffzero, mul_zero]
      simp
  · have hp : 2 ≤ 2 * a + b := by omega
    by_cases hbq : b ≤ n - a
    · have hpow := positivePrefix_pow_coeff_natDegree_le prior n b (n-a) d hprior
      calc
        (residualTerm Rshift s n a b prior).natDegree
            ≤ ((Rshift.coeff b).coeff a).natDegree +
                (s ^ (2*a+b-2)).natDegree +
                  (((positivePrefix prior n)^b).coeff (n-a)).natDegree := by
              unfold residualTerm
              exact Polynomial.natDegree_mul_le.trans
                (Nat.add_le_add_right Polynomial.natDegree_mul_le _)
        _ ≤ d + (2*a+b-2) * (d-1) + (2*(n-a)-b)*d := by
              gcongr
              exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ hs)
        _ ≤ d + (2*a+b-2) * d + (2*(n-a)-b)*d := by
              gcongr <;> omega
        _ = (2*n-1)*d := by
              calc
                _ = (1 + (2*a+b-2) + (2*(n-a)-b)) * d := by ring
                _ = _ := by congr 1 <;> omega
    · have hlt : n - a < b := by omega
      rw [residualTerm, positivePrefix_pow_coeff_eq_zero_of_lt prior n b (n-a) hlt,
        mul_zero]
      simp

theorem residualTerm_degreeX_le
    (Rshift : F[X][X][X][X]) (s : F[X][X]) (n a b D : ℕ)
    (hn : 0 < n) (ha : a ≤ n)
    (hcoeff : Bivariate.degreeX ((Rshift.coeff b).coeff a) ≤ D)
    (hs : Bivariate.degreeX s ≤ D)
    (prior : ℕ → F[X][X])
    (hprior : ∀ i, 0 < i → i < n →
      Bivariate.degreeX (prior i) ≤ (2 * i - 1) * D) :
    Bivariate.degreeX (residualTerm Rshift s n a b prior) ≤ (2 * n - 1) * D := by
  by_cases hsmall : 2 * a + b < 2
  · have ha0 : a = 0 := by omega
    subst a
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    · have hcoeffzero : ((positivePrefix prior n) ^ 0).coeff (n - 0) = 0 := by
        rw [pow_zero, Nat.sub_zero, Polynomial.coeff_one, if_neg hn.ne']
      unfold residualTerm
      rw [hcoeffzero, mul_zero]
      simp [Bivariate.degreeX]
    · have hcoeffzero : ((positivePrefix prior n) ^ 1).coeff (n - 0) = 0 := by
        rw [pow_one, Nat.sub_zero, positivePrefix_coeff_self]
      unfold residualTerm
      rw [hcoeffzero, mul_zero]
      simp [Bivariate.degreeX]
  · have hp : 2 ≤ 2 * a + b := by omega
    by_cases hbq : b ≤ n - a
    · have hpow := positivePrefix_pow_coeff_degreeX_le prior n b (n-a) D hprior
      calc
        Bivariate.degreeX (residualTerm Rshift s n a b prior)
            ≤ Bivariate.degreeX ((Rshift.coeff b).coeff a) +
                Bivariate.degreeX (s ^ (2*a+b-2)) +
                  Bivariate.degreeX (((positivePrefix prior n)^b).coeff (n-a)) := by
              unfold residualTerm
              exact (Bivariate.degreeX_mul_le _ _).trans
                (Nat.add_le_add_right (Bivariate.degreeX_mul_le _ _) _)
        _ ≤ D + (2*a+b-2) * D + (2*(n-a)-b)*D := by
              gcongr
              exact (degreeX_pow_le s _).trans (Nat.mul_le_mul_left _ hs)
        _ = (2*n-1)*D := by
              calc
                _ = (1 + (2*a+b-2) + (2*(n-a)-b)) * D := by ring
                _ = _ := by congr 1 <;> omega
    · have hlt : n - a < b := by omega
      rw [residualTerm, positivePrefix_pow_coeff_eq_zero_of_lt prior n b (n-a) hlt,
        mul_zero]
      simp [Bivariate.degreeX]

theorem numeratorStep_natDegree_le
    (Rshift : F[X][X][X]) (s : F[X]) (dY n : ℕ)
    (hn : 0 < n) (hdY : 0 < dY)
    (hcoeff : ∀ b a, b ≤ dY → a ≤ n →
      ((Rshift.coeff b).coeff a).natDegree ≤ dY)
    (hs : s.natDegree ≤ dY - 1)
    (prior : ℕ → F[X])
    (hprior : ∀ i, 0 < i → i < n →
      (prior i).natDegree ≤ (2 * i - 1) * dY) :
    (numeratorStep Rshift s dY n prior).natDegree ≤ (2*n-1)*dY := by
  unfold numeratorStep
  rw [Polynomial.natDegree_neg]
  apply YZFactorCap.natDegree_sum_le_of_forall
  intro a ha
  apply YZFactorCap.natDegree_sum_le_of_forall
  intro b hb
  exact residualTerm_natDegree_le Rshift s n a b dY hn
    (by simpa using ha) hdY (hcoeff b a (by simpa using hb) (by simpa using ha))
    hs prior hprior

theorem numeratorStep_degreeX_le
    (Rshift : F[X][X][X][X]) (s : F[X][X]) (dCap n D : ℕ)
    (hn : 0 < n)
    (hcoeff : ∀ b a, b ≤ dCap → a ≤ n →
      Bivariate.degreeX ((Rshift.coeff b).coeff a) ≤ D)
    (hs : Bivariate.degreeX s ≤ D)
    (prior : ℕ → F[X][X])
    (hprior : ∀ i, 0 < i → i < n →
      Bivariate.degreeX (prior i) ≤ (2 * i - 1) * D) :
    Bivariate.degreeX (numeratorStep Rshift s dCap n prior) ≤ (2*n-1)*D := by
  unfold numeratorStep
  rw [degreeX_neg]
  apply YZFactorCap.degreeX_sum_le_of_forall
  intro a ha
  apply YZFactorCap.degreeX_sum_le_of_forall
  intro b hb
  exact residualTerm_degreeX_le Rshift s n a b D hn (by simpa using ha)
    (hcoeff b a (by simpa using hb) (by simpa using ha)) hs prior hprior

theorem numerators_natDegree_le
    (Rshift : F[X][X][X]) (s : F[X]) (dY : ℕ) (hdY : 0 < dY)
    (hcoeff : ∀ n b a, b ≤ dY → a ≤ n →
      ((Rshift.coeff b).coeff a).natDegree ≤ dY)
    (hs : s.natDegree ≤ dY - 1) :
    ∀ n, 0 < n → (numerators Rshift s dY n).natDegree ≤ (2*n-1)*dY := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp at hn
      | succ t =>
          rw [numerators_succ]
          apply numeratorStep_natDegree_le Rshift s dY (t+1) (by omega) hdY
            (hcoeff (t+1)) hs
          intro i hi hit
          change (if i ≤ t then numerators Rshift s dY i else 0).natDegree ≤ _
          rw [if_pos (by omega)]
          exact ih i (by omega) hi

theorem numerators_degreeX_le
    (Rshift : F[X][X][X][X]) (s : F[X][X]) (dCap D : ℕ)
    (hcoeff : ∀ n b a, b ≤ dCap → a ≤ n →
      Bivariate.degreeX ((Rshift.coeff b).coeff a) ≤ D)
    (hs : Bivariate.degreeX s ≤ D) :
    ∀ n, 0 < n → Bivariate.degreeX (numerators Rshift s dCap n) ≤ (2*n-1)*D := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp at hn
      | succ t =>
          rw [numerators_succ]
          apply numeratorStep_degreeX_le Rshift s dCap (t+1) D (by omega)
            (hcoeff (t+1)) hs
          intro i hi hit
          change Bivariate.degreeX
            (if i ≤ t then numerators Rshift s dCap i else 0) ≤ _
          rw [if_pos (by omega)]
          exact ih i (by omega) hi

end

end ProximityPrize.SubmissionLower.UniversalNumerator

open Polynomial

namespace ProximityPrize.SubmissionLower.UniversalNumerator

noncomputable section

variable {L : Type*} [Field L]

/-- Coefficientwise odd-exponent scaling is ordinary variable scaling after
multiplying the whole positive prefix by one copy of the slope. -/
theorem positivePrefix_odd_scaled
    (s : L) (N c : ℕ → L) (n : ℕ)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    Polynomial.C s * positivePrefix N n =
      (positivePrefix c n).comp (Polynomial.C (s ^ 2) * Polynomial.X) := by
  ext i
  rw [Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  rw [positivePrefix_coeff, positivePrefix_coeff]
  by_cases hi : 0 < i ∧ i < n
  · rw [if_pos hi, if_pos hi, hrel i hi.1 hi.2]
    calc
      s * (s ^ (2 * i - 1) * c i) = s ^ (1 + (2 * i - 1)) * c i := by
        rw [pow_add]
        ring
      _ = s ^ (2 * i) * c i := by congr 2 <;> omega
      _ = c i * (s ^ 2) ^ i := by rw [pow_mul]; ring
  · rw [if_neg hi, if_neg hi]
    simp

/-- Power-coefficient form of `positivePrefix_odd_scaled`.  This avoids any
explicit enumeration of positive compositions and is the useful cancellation
identity in the universal numerator recurrence. -/
theorem positivePrefix_pow_cross_scaled
    (s : L) (N c : ℕ → L) (n b u : ℕ)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    s ^ b * ((positivePrefix N n) ^ b).coeff u =
      s ^ (2 * u) * ((positivePrefix c n) ^ b).coeff u := by
  let q : L[X] := Polynomial.C (s ^ 2) * Polynomial.X
  have hcomp_all : ∀ m : ℕ, ((positivePrefix c n) ^ m).comp q =
      ((positivePrefix c n).comp q) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp only [pow_succ, Polynomial.mul_comp, ih]
  have hcomp := hcomp_all b
  have hp := congrArg (fun p : L[X] => p ^ b)
    (positivePrefix_odd_scaled s N c n hrel)
  have hpoly : Polynomial.C (s ^ b) * (positivePrefix N n) ^ b =
      ((positivePrefix c n) ^ b).comp q := by
    calc
      Polynomial.C (s ^ b) * (positivePrefix N n) ^ b =
          (Polynomial.C s) ^ b * (positivePrefix N n) ^ b := by rw [Polynomial.C_pow]
      _ = (Polynomial.C s * positivePrefix N n) ^ b := by rw [mul_pow]
      _ = ((positivePrefix c n).comp q) ^ b := hp
      _ = ((positivePrefix c n) ^ b).comp q := hcomp.symm
  have hc := congrArg (fun p : L[X] => p.coeff u) hpoly
  simp only [Polynomial.coeff_C_mul, q, Polynomial.comp_C_mul_X_coeff] at hc
  rw [pow_mul]
  simpa [mul_comm] using hc

/-- A polynomial with zero constant coefficient has no term below the number
of factors in any positive power. -/
theorem coeff_pow_eq_zero_below_of_coeff_zero
    (p : L[X]) (hp0 : p.coeff 0 = 0) :
    ∀ b u : ℕ, u < b → (p ^ b).coeff u = 0 := by
  intro b
  induction b with
  | zero => intro u hu; omega
  | succ b ih =>
      intro u hu
      rw [pow_succ, Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ hij
      have hijsum : i + j = u := Finset.mem_antidiagonal.mp hij
      by_cases hib : i < b
      · rw [ih i hib, zero_mul]
      · have hju : j = 0 := by omega
        subst j
        rw [hp0, mul_zero]

theorem positivePrefix_pow_coeff_zero_of_lt
    (c : ℕ → L) (n b u : ℕ) (hu : u < b) :
    ((positivePrefix c n) ^ b).coeff u = 0 := by
  apply coeff_pow_eq_zero_below_of_coeff_zero
  · rw [positivePrefix_coeff]
    simp
  · exact hu

/-- Cancelled form of the cross-scaling identity. -/
theorem positivePrefix_pow_coeff_scaled
    (s : L) (hs : s ≠ 0) (N c : ℕ → L) (n b u : ℕ)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    ((positivePrefix N n) ^ b).coeff u =
      s ^ (2 * u - b) * ((positivePrefix c n) ^ b).coeff u := by
  by_cases hub : u < b
  · rw [positivePrefix_pow_coeff_zero_of_lt N n b u hub,
      positivePrefix_pow_coeff_zero_of_lt c n b u hub]
    simp
  · have hbu : b ≤ u := Nat.le_of_not_gt hub
    apply mul_left_cancel₀ (pow_ne_zero b hs)
    rw [positivePrefix_pow_cross_scaled s N c n b u hrel]
    have hexp : b + (2 * u - b) = 2 * u := by omega
    calc
      s ^ (2 * u) * ((positivePrefix c n) ^ b).coeff u =
          s ^ (b + (2 * u - b)) * ((positivePrefix c n) ^ b).coeff u := by
            rw [hexp]
      _ = s ^ b *
          (s ^ (2 * u - b) * ((positivePrefix c n) ^ b).coeff u) := by
            rw [pow_add]
            ring

/-- Each nonzero residual term acquires the common clearing factor
`s^(2*n-2)`.  The two low-weight exceptional pairs `(0,0)` and `(0,1)` vanish
because the positive prefix has no constant/current coefficient. -/
theorem residualTerm_scaled
    (Rshift : L[X][X]) (s : L) (hs : s ≠ 0) (d n a b : ℕ)
    (N c : ℕ → L) (hn : 1 ≤ n) (ha : a ≤ n)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    residualTerm Rshift s n a b N =
      s ^ (2 * n - 2) *
        (((Rshift.coeff b).coeff a) *
          ((positivePrefix c n) ^ b).coeff (n - a)) := by
  unfold residualTerm
  rw [positivePrefix_pow_coeff_scaled s hs N c n b (n-a) hrel]
  by_cases hbu : b ≤ n - a
  · by_cases hweight : 2 ≤ 2 * a + b
    · have hexp : (2 * a + b - 2) + (2 * (n - a) - b) = 2 * n - 2 := by
        omega
      calc
        (Rshift.coeff b).coeff a * s ^ (2 * a + b - 2) *
            (s ^ (2 * (n - a) - b) *
              ((positivePrefix c n) ^ b).coeff (n - a)) =
            (Rshift.coeff b).coeff a *
              s ^ ((2 * a + b - 2) + (2 * (n - a) - b)) *
                ((positivePrefix c n) ^ b).coeff (n - a) := by
              rw [pow_add]
              ring
        _ = s ^ (2 * n - 2) *
            ((Rshift.coeff b).coeff a *
              ((positivePrefix c n) ^ b).coeff (n - a)) := by
              rw [hexp]
              ring
    · have hcases : (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        simp [Polynomial.coeff_one, hn0]
      · simp only [pow_one, Nat.zero_mul, Nat.zero_add, Nat.sub_zero,
          positivePrefix_coeff_self, mul_zero, zero_mul]
  · have hz := positivePrefix_pow_coeff_zero_of_lt c n b (n-a) (by omega)
    rw [hz]
    simp

/-- The residual coefficient with the current coefficient omitted. -/
def prefixResidualCoeff (Rshift : L[X][X]) (d n : ℕ)
    (c : ℕ → L) : L :=
  ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (d + 1),
    ((Rshift.coeff b).coeff a) *
      ((positivePrefix c n) ^ b).coeff (n - a)

/-- After specialization to a field, `numeratorStep` is exactly the omitted
current residual coefficient cleared by `s^(2*n-2)`. -/
theorem numeratorStep_scaled
    (Rshift : L[X][X]) (s : L) (hs : s ≠ 0) (d n : ℕ)
    (N c : ℕ → L) (hn : 1 ≤ n)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    numeratorStep Rshift s d n N =
      -(s ^ (2 * n - 2) * prefixResidualCoeff Rshift d n c) := by
  classical
  unfold numeratorStep prefixResidualCoeff
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact residualTerm_scaled Rshift s hs d n a b N c hn
    (by simpa using (Finset.mem_range.mp ha)) hrel

end

end ProximityPrize.SubmissionLower.UniversalNumerator

open Polynomial

namespace ProximityPrize.SubmissionLower.UniversalNumerator

noncomputable section

variable {L : Type*} [Field L]

/-- Coefficient expansion of an outer evaluation, padded to any declared
outer-degree cap. -/
theorem coeff_eval_eq_prefixResidualCoeff
    (Rshift : L[X][X]) (d n : ℕ) (c : ℕ → L)
    (hdeg : Rshift.natDegree ≤ d) :
    (Rshift.eval (positivePrefix c n)).coeff n =
      prefixResidualCoeff Rshift d n c := by
  classical
  rw [Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le hdeg) (positivePrefix c n)]
  rw [coeff_finset_sum]
  simp_rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold prefixResidualCoeff
  rw [Finset.sum_comm]

theorem shiftMap_zero_eq :
    ProximityPrize.SubmissionLower.FiniteHensel.shiftMap (0 : L) =
      RingHom.id L[X] := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply]
  · simp [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply]

/-- Evaluation coefficient `n` only depends on input coefficients through
`n`; higher terms of an exact root polynomial are irrelevant. -/
theorem coeff_eval_eq_of_coeff_eq_up_to
    (Rshift : L[X][X]) (P Q : L[X]) (n : ℕ)
    (hcoeff : ∀ i, i ≤ n → P.coeff i = Q.coeff i) :
    (Rshift.eval P).coeff n = (Rshift.eval Q).coeff n := by
  have hdiff := ProximityPrize.SubmissionLower.FiniteHensel.eval_sub_eval_eq_mul_dividedDifference
    Rshift P Q
  have hlow : ∀ i, i ≤ n → (P - Q).coeff i = 0 := by
    intro i hi
    simp [hcoeff i hi]
  have hmul : ((P - Q) *
      ProximityPrize.SubmissionLower.FiniteHensel.dividedDifference Rshift P Q).coeff n = 0 := by
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i,j⟩ hij
    rw [hlow i (by have := Finset.mem_antidiagonal.mp hij; omega), zero_mul]
  have hzero : (Rshift.eval P - Rshift.eval Q).coeff n = 0 := by
    rw [hdiff]
    exact hmul
  simpa only [Polynomial.coeff_sub, sub_eq_zero] using hzero

/-- Every diagonal coefficient of the truncated input of an exact polynomial
root vanishes, with no degree bound on the root polynomial. -/
theorem residual_diagonal_zero_of_exact
    (Rshift : L[X][X]) (V : L[X]) (n : ℕ)
    (hExact : Rshift.eval V = 0) :
    (ProximityPrize.SubmissionLower.FiniteHensel.residual
      Rshift 0 (fun i => V.coeff i) n).coeff n = 0 := by
  unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
  rw [shiftMap_zero_eq]
  change (Rshift.eval
    (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries
      (fun i => V.coeff i) n)).coeff n = 0
  have heq := coeff_eval_eq_of_coeff_eq_up_to Rshift V
    (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries
      (fun i => V.coeff i) n) n (by
        intro i hi
        symm
        exact ProximityPrize.SubmissionLower.FiniteHensel.coeff_truncSeries _ _ _ hi)
  rw [← heq, hExact]
  simp

/-- Truncating a zero-constant sequence immediately before index `n` is the
positive prefix used by the universal recurrence. -/
theorem truncSeries_cut_eq_positivePrefix
    (c : ℕ → L) (n : ℕ) (hc0 : c 0 = 0) :
    ProximityPrize.SubmissionLower.FiniteHensel.truncSeries
      (fun i => if i < n then c i else 0) n = positivePrefix c n := by
  ext i
  by_cases hin : i ≤ n
  · rw [ProximityPrize.SubmissionLower.FiniteHensel.coeff_truncSeries _ _ _ hin,
      positivePrefix_coeff]
    by_cases hi0 : i = 0
    · subst i
      simp [hc0]
    · by_cases hlt : i < n
      · simp [hi0, hlt]
      · simp [hi0, hlt]
  · rw [positivePrefix_coeff]
    unfold ProximityPrize.SubmissionLower.FiniteHensel.truncSeries
    simp [hin, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    intro _ hlt
    exact (hin hlt.le).elim

/-- The exact-root coefficient equation with the current coefficient omitted.
This is the finite implicit-function recurrence in the target field. -/
theorem slope_mul_coeff_eq_neg_prefixResidual
    (Rshift : L[X][X]) (s : L) (d n : ℕ) (c : ℕ → L)
    (hn : 1 ≤ n) (hc0 : c 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      Rshift 0 0 = s)
    (hvanish :
      (ProximityPrize.SubmissionLower.FiniteHensel.residual
        Rshift 0 c n).coeff n = 0) :
    s * c n = -prefixResidualCoeff Rshift d n c := by
  let cut : ℕ → L := fun i => if i < n then c i else 0
  have hcut0 : cut 0 = 0 := by simp [cut, hn, hc0]
  have hprev : ∀ i, i < n → c i = cut i := by
    intro i hi
    simp [cut, hi]
  have hrec := ProximityPrize.SubmissionLower.FiniteHensel.coefficientRecurrence
    Rshift 0 0 c cut n n (le_refl n) hc0 hcut0 hprev
  have hcutResidual :
      (ProximityPrize.SubmissionLower.FiniteHensel.residual
        Rshift 0 cut n).coeff n = prefixResidualCoeff Rshift d n c := by
    unfold ProximityPrize.SubmissionLower.FiniteHensel.residual
    rw [shiftMap_zero_eq]
    change (Rshift.eval
      (ProximityPrize.SubmissionLower.FiniteHensel.truncSeries cut n)).coeff n = _
    rw [show ProximityPrize.SubmissionLower.FiniteHensel.truncSeries cut n =
      positivePrefix c n by
        simpa [cut] using truncSeries_cut_eq_positivePrefix c n hc0]
    exact coeff_eval_eq_prefixResidualCoeff Rshift d n c hdeg
  rw [hvanish, hcutResidual, hslope] at hrec
  have hcutn : cut n = 0 := by simp [cut]
  rw [hcutn, sub_zero] at hrec
  simpa only [zero_sub] using hrec.symm

/-- One induction step: the universal numerator specializes to the exact
Taylor coefficient times `s^(2*n-1)`. -/
theorem numeratorStep_eq_slope_pow_mul_coeff
    (Rshift : L[X][X]) (s : L) (hs : s ≠ 0) (d n : ℕ)
    (N c : ℕ → L) (hn : 1 ≤ n) (hc0 : c 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      Rshift 0 0 = s)
    (hvanish :
      (ProximityPrize.SubmissionLower.FiniteHensel.residual
        Rshift 0 c n).coeff n = 0)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    numeratorStep Rshift s d n N = s ^ (2 * n - 1) * c n := by
  rw [numeratorStep_scaled Rshift s hs d n N c hn hrel]
  have hcoeff := slope_mul_coeff_eq_neg_prefixResidual
    Rshift s d n c hn hc0 hdeg hslope hvanish
  have hexp : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  calc
    -(s ^ (2 * n - 2) * prefixResidualCoeff Rshift d n c) =
        s ^ (2 * n - 2) * (-prefixResidualCoeff Rshift d n c) := by ring
    _ = s ^ (2 * n - 2) * (s * c n) := by rw [hcoeff]
    _ = s ^ (2 * n - 1) * c n := by rw [hexp, pow_add, pow_one]; ring

/-- Full course-of-values representation in a target field.  The only input
from an exact root is the diagonal residual vanishing at each truncation. -/
theorem numerators_eq_slope_pow_mul_coeff
    (Rshift : L[X][X]) (s : L) (hs : s ≠ 0) (d : ℕ)
    (c : ℕ → L) (hc0 : c 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      Rshift 0 0 = s)
    (hvanish : ∀ n, 1 ≤ n →
      (ProximityPrize.SubmissionLower.FiniteHensel.residual
        Rshift 0 c n).coeff n = 0) :
    ∀ n, 1 ≤ n → numerators Rshift s d n = s ^ (2 * n - 1) * c n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [numerators_succ]
      apply numeratorStep_eq_slope_pow_mul_coeff
        Rshift s hs d (t + 1)
          (fun i => if i ≤ t then numerators Rshift s d i else 0)
          c (by omega) hc0 hdeg hslope (hvanish (t + 1) (by omega))
      intro i hi0 hit
      have hit' : i ≤ t := by omega
      rw [if_pos hit']
      exact ih i (by omega) hi0

/-- Exact polynomial-root specialization of the full universal numerator
sequence. -/
theorem numerators_eq_slope_pow_mul_root_coeff
    (Rshift : L[X][X]) (V : L[X]) (s : L) (hs : s ≠ 0) (d : ℕ)
    (hV0 : V.coeff 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      Rshift 0 0 = s)
    (hExact : Rshift.eval V = 0) :
    ∀ n, 1 ≤ n → numerators Rshift s d n =
      s ^ (2 * n - 1) * V.coeff n := by
  apply numerators_eq_slope_pow_mul_coeff Rshift s hs d
    (fun i => V.coeff i) hV0 hdeg hslope
  intro n _
  exact residual_diagonal_zero_of_exact Rshift V n hExact

end

end ProximityPrize.SubmissionLower.UniversalNumerator


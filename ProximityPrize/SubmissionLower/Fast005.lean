import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Fast001
set_option Elab.async false

section PackSource_FrobeniusLocator
set_option autoImplicit true
/-! An isolated Frobenius-locator feasibility probe. No benchmark sources are modified. -/
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def weight (x : ι → F) (i : ι) : F :=
  (∏ j ∈ (Finset.univ : Finset ι).erase i, (x i - x j))⁻¹

def syndrome (x : ι → F) (u : ι → F) (j : ℕ) : F :=
  ∑ i, weight x i * u i * x i ^ j

theorem weighted_eval_sum_zero (x : ι → F) (hx : Function.Injective x)
    (q : F[X]) (hq : q.degree < (Fintype.card ι - 1 : ℕ)) :
    ∑ i, weight x i * q.eval (x i) = 0 := by
  have hlt : q.degree < (Fintype.card ι : ℕ) :=
    hq.trans_le (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1)
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := x)
    (fun a _ b _ hab => hx hab) (by simpa using hlt)
  rw [Finset.card_univ, Polynomial.coeff_eq_zero_of_degree_lt hq] at h
  simpa [weight, div_eq_mul_inv, mul_comm] using h.symm

def hankel (x : ι → F) (u v : ι → F) (L t : ℕ) :
    Matrix (Fin L) (Fin (t + 1)) F[X] :=
  fun i j => C (syndrome x u (i.val + j.val)) +
    X * C (syndrome x v (i.val + j.val))

def locator (x : ι → F) (S : Finset ι) : F[X] :=
  ∏ i ∈ S, (X - C (x i))

theorem locator_monic (x : ι → F) (S : Finset ι) : (locator x S).Monic :=
  Polynomial.monic_prod_of_monic S _ (fun _ _ => monic_X_sub_C _)

theorem locator_natDegree (x : ι → F) (S : Finset ι) :
    (locator x S).natDegree = S.card := by
  rw [locator, Polynomial.natDegree_prod_of_monic S _ (fun _ _ => monic_X_sub_C _)]
  simp

theorem locator_eval_zero (x : ι → F) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    (locator x S).eval (x i) = 0 := by
  simp only [locator, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero hi (sub_self _)

theorem sum_coeff_eval (E : F[X]) (t : ℕ) (hE : E.natDegree ≤ t) (a : F) :
    (∑ j : Fin (t + 1), E.coeff j.val * a ^ j.val) = E.eval a := by
  rw [Fin.sum_univ_eq_sum_range (fun j => E.coeff j * a ^ j) (t + 1)]
  exact (Polynomial.eval_eq_sum_range' (by omega) a).symm

/-- All ordinary Hankel equations follow from pointwise annihilation of the errors. -/
theorem hankel_annihilates (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (γ : F) (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (P E : F[X]) (hP : P.degree < k) (hE : E.natDegree ≤ t)
    (hagree : ∀ a, E.eval (x a) * (u a + γ * v a) = E.eval (x a) * P.eval (x a)) :
    (fun i j => ((hankel x u v L t) i j).eval γ) *ᵥ
      (fun j : Fin (t + 1) => E.coeff j.val) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, hankel, eval_add, eval_mul, eval_C, eval_X,
    Pi.zero_apply]
  change (∑ j : Fin (t + 1),
    ((syndrome x u (i.val + j.val)) + γ * syndrome x v (i.val + j.val)) *
      E.coeff j.val) = 0
  have hsum : (∑ j : Fin (t + 1),
      ((syndrome x u (i.val + j.val)) + γ * syndrome x v (i.val + j.val)) *
        E.coeff j.val) =
      ∑ a, weight x a * (E.eval (x a) * (u a + γ * v a)) * x a ^ i.val := by
    simp only [syndrome, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← sum_coeff_eval E t hE (x a)]
    simp only [Finset.sum_mul, Finset.mul_sum, pow_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  simp_rw [hagree]
  have hq : (E * P * X ^ i.val).degree < (↑(Fintype.card ι - 1) : WithBot ℕ) := by
    by_cases hp0 : P = 0
    · simp [hp0]
    have hpn : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hP
    have hn : (E * P * X ^ i.val).natDegree ≤ t + P.natDegree + i.val := by
      calc
        _ ≤ (E * P).natDegree + (X ^ i.val : F[X]).natDegree := natDegree_mul_le
        _ ≤ (E.natDegree + P.natDegree) + i.val := by
          simpa using Nat.add_le_add_right (natDegree_mul_le (p := E) (q := P)) i.val
        _ ≤ t + P.natDegree + i.val := by omega
    have hb : (E * P * X ^ i.val).natDegree < Fintype.card ι - 1 := by
      have := i.isLt
      omega
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hb)
  have hz := weighted_eval_sum_zero x hx (E * P * X ^ i.val) hq
  simpa only [eval_mul, eval_pow, eval_X, mul_assoc] using hz

variable (p : ℕ) [ExpChar F p]

theorem weight_frobenius (x : ι → F) (hfixed : ∀ i, x i ^ p = x i) (i : ι) :
    frobenius F p (weight x i) = weight x i := by
  simp only [weight, map_inv₀, map_prod, map_sub, frobenius_def, hfixed]

/-- The conjugate syndrome block is literally the syndrome of the conjugate word. -/
theorem syndrome_frobenius (x : ι → F) (hfixed : ∀ i, x i ^ p = x i)
    (u : ι → F) (j : ℕ) :
    syndrome x (fun i => u i ^ p) j = (syndrome x u j) ^ p := by
  change (∑ i, weight x i * u i ^ p * x i ^ j) =
    frobenius F p (∑ i, weight x i * u i * x i ^ j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, map_pow, weight_frobenius p x hfixed i]
  simp only [frobenius_def, hfixed]

/-- This also records a literal base-field coefficient representation. -/
theorem locator_map {B : Type*} [Field B] (φ : B →+* F) (x : ι → B) (S : Finset ι) :
    (locator x S).map φ = locator (fun i => φ (x i)) S := by
  simp [locator, Polynomial.map_prod]

theorem locator_map_frobenius (x : ι → F) (hfixed : ∀ i, x i ^ p = x i)
    (S : Finset ι) : (locator x S).map (frobenius F p) = locator x S := by
  simp [locator, Polynomial.map_prod, hfixed, frobenius_def]

def stacked (x : ι → F) (u v : ι → F) (L t : ℕ) :
    Matrix (Fin 2 × Fin L) (Fin (t + 1)) F[X] :=
  fun i j => if i.1 = 0 then hankel x u v L t i.2 j else
    C ((syndrome x u (i.2.val + j.val)) ^ p) +
      X ^ p * C ((syndrome x v (i.2.val + j.val)) ^ p)

theorem locator_annihilates_stacked (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F) (γ : F)
    (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (P : F[X]) (hP : P.degree < k) (S : Finset ι) (hS : S.card ≤ t)
    (hagree : ∀ a, a ∉ S → u a + γ * v a = P.eval (x a)) :
    (fun i j => ((stacked p x u v L t) i j).eval γ) *ᵥ
      (fun j : Fin (t + 1) => (locator x S).coeff j.val) = 0 := by
  have hE : (locator x S).natDegree ≤ t := (locator_natDegree x S).trans_le hS
  have ha : ∀ a, (locator x S).eval (x a) * (u a + γ * v a) =
      (locator x S).eval (x a) * P.eval (x a) := by
    intro a
    by_cases h : a ∈ S
    · simp [locator_eval_zero x S a h]
    · rw [hagree a h]
  have hfirst := hankel_annihilates x hx u v γ k L t hsize P (locator x S) hP hE ha
  have hcoeff : ∀ j, frobenius F p ((locator x S).coeff j) = (locator x S).coeff j := by
    intro j
    have hc := congrArg (fun q : F[X] => q.coeff j) (locator_map_frobenius p x hfixed S)
    simpa only [Polynomial.coeff_map] using hc
  funext i
  rcases i with ⟨b, i⟩
  fin_cases b
  · simpa [stacked, Matrix.mulVec, dotProduct, hankel] using congrFun hfirst i
  · have hh := congrArg (frobenius F p) (congrFun hfirst i)
    simp only [Matrix.mulVec, dotProduct, hankel, eval_add, eval_mul, eval_C, eval_X,
      Pi.zero_apply, map_sum, map_mul, map_add, map_zero, hcoeff] at hh
    simpa [stacked, Matrix.mulVec, dotProduct, frobenius_def, mul_comm] using hh

end
end FrobeniusLocator
end PackSource_FrobeniusLocator

section PackSource_FullRankCount
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace FrobeniusLocator
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
local instance decidableFullRank (P : Prop) : Decidable P := Classical.propDecidable P

/-- A polynomial of degree below k agrees outside at most t nodes. -/
def Decodable (x : ι → F) (u v : ι → F) (k t : ℕ) (γ : F) : Prop :=
  ∃ P : F[X], P.degree < k ∧
    (Finset.univ.filter (fun i => u i + γ * v i ≠ P.eval (x i))).card ≤ t

def minorPolynomial {row col : Type*} [Fintype col] [DecidableEq col]
    (M : Matrix row col F[X]) (rows : col → row) : F[X] :=
  Matrix.det (fun i j => M (rows i) j)

theorem det_eval_eq {col : Type*} [Fintype col] [DecidableEq col]
    (M : Matrix col col F[X]) (γ : F) :
    M.det.eval γ = Matrix.det (fun i j => (M i j).eval γ) :=
  (Polynomial.evalRingHom γ).map_det M

variable (p : ℕ) [ExpChar F p]

/-- A nonzero maximal minor vanishes at every decodable challenge. -/
theorem decodable_implies_minor_root (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F)
    (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (rows : Fin (t + 1) → Fin 2 × Fin L) (γ : F)
    (hγ : Decodable x u v k t γ) :
    (minorPolynomial (stacked p x u v L t) rows).eval γ = 0 := by
  classical
  obtain ⟨P, hP, hcard⟩ := hγ
  let S := Finset.univ.filter (fun i => u i + γ * v i ≠ P.eval (x i))
  have hS : S.card ≤ t := hcard
  have hagree : ∀ i, i ∉ S → u i + γ * v i = P.eval (x i) := by
    intro i hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have hk := locator_annihilates_stacked p x hx hfixed u v γ k L t hsize P hP S hS hagree
  have hkm : (fun i j => ((stacked p x u v L t) (rows i) j).eval γ) *ᵥ
      (fun j : Fin (t + 1) => (locator x S).coeff j.val) = 0 := by
    funext i
    exact congrFun hk (rows i)
  have hc : (locator x S).coeff S.card = 1 := by
    rw [← locator_natDegree x S]
    exact (locator_monic x S).coeff_natDegree
  rw [minorPolynomial, det_eval_eq (fun i j : Fin (t + 1) => stacked p x u v L t (rows i) j) γ]
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hkm
    (i := ⟨S.card, by omega⟩) (by simpa only [hc] using (one_mem (nonZeroDivisors F)))

theorem decodable_finset_card_le_minor_degree (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F)
    (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (rows : Fin (t + 1) → Fin 2 × Fin L)
    (hminor : minorPolynomial (stacked p x u v L t) rows ≠ 0)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Decodable x u v k t γ) :
    Γ.card ≤ (minorPolynomial (stacked p x u v L t) rows).natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro γ hγ
  exact (Polynomial.mem_roots hminor).mpr
    (decodable_implies_minor_root p x hx hfixed u v k L t hsize rows γ (hΓ γ hγ))

/-- All A-close slopes, including the good ones, are bounded by one minor degree. -/
theorem full_rank_Aclose_count [Fintype F] (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F)
    (k A : ℕ) (hkA : k ≤ A) (hAn : A ≤ Fintype.card ι)
    (rows : Fin (Fintype.card ι - A + 1) → Fin 2 × Fin (A - k))
    (hminor : minorPolynomial
      (stacked p x u v (A - k) (Fintype.card ι - A)) rows ≠ 0) :
    (Finset.univ.filter (fun γ => Decodable x u v k (Fintype.card ι - A) γ)).card ≤
      (minorPolynomial (stacked p x u v (A - k) (Fintype.card ι - A)) rows).natDegree := by
  classical
  apply decodable_finset_card_le_minor_degree p x hx hfixed u v k (A - k)
    (Fintype.card ι - A) (by omega) rows hminor
  intro γ hγ
  exact (Finset.mem_filter.mp hγ).2

end
end FrobeniusLocator
end PackSource_FullRankCount

section PackSource_MinorDegree
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators

variable {F : Type*} [Field F]
local instance decidableMinorDegree (P : Prop) : Decidable P := Classical.propDecidable P

/-- A generic determinant bound, measured by row degrees. -/
theorem natDegree_det_le_row_sum {c : Type*} [Fintype c] [DecidableEq c]
    (M : Matrix c c F[X]) (d : c → ℕ) (hM : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hs : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree =
      (∏ i, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, natDegree_neg]
  rw [hs]
  calc
    _ ≤ ∑ i, (M (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, d (σ i) := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = ∑ i, d i := Equiv.sum_comp σ d

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hankel_entry_natDegree (x : ι → F) (u v : ι → F) (L t : ℕ)
    (i : Fin L) (j : Fin (t + 1)) : (hankel x u v L t i j).natDegree ≤ 1 := by
  unfold hankel
  compute_degree

theorem stacked_entry_natDegree (p : ℕ) [ExpChar F p] (x : ι → F) (u v : ι → F)
    (L t : ℕ) (i : Fin 2 × Fin L) (j : Fin (t + 1)) :
    (stacked p x u v L t i j).natDegree ≤ if i.1 = 0 then 1 else p := by
  unfold stacked
  split_ifs with h
  · exact hankel_entry_natDegree x u v L t i.2 j
  · compute_degree

theorem minor_natDegree_le_row_sum (p : ℕ) [ExpChar F p] (x : ι → F)
    (u v : ι → F) (L t : ℕ) (rows : Fin (t + 1) → Fin 2 × Fin L) :
    (minorPolynomial (stacked p x u v L t) rows).natDegree ≤
      ∑ i : Fin (t + 1), if (rows i).1 = 0 then 1 else p := by
  exact natDegree_det_le_row_sum _ _ (fun i j => stacked_entry_natDegree p x u v L t (rows i) j)

theorem minor_natDegree_le (p : ℕ) [ExpChar F p] (hp : 1 ≤ p) (x : ι → F)
    (u v : ι → F) (L t : ℕ) (rows : Fin (t + 1) → Fin 2 × Fin L) :
    (minorPolynomial (stacked p x u v L t) rows).natDegree ≤ p * (t + 1) := by
  apply (minor_natDegree_le_row_sum p x u v L t rows).trans
  calc
    _ ≤ ∑ _i : Fin (t + 1), p := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> omega
    _ = p * (t + 1) := by simp [Nat.mul_comm]

theorem full_rank_Aclose_count_explicit [Fintype F] (p : ℕ) [ExpChar F p]
    (hp : 1 ≤ p) (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F)
    (k A : ℕ) (hkA : k ≤ A) (hAn : A ≤ Fintype.card ι)
    (rows : Fin (Fintype.card ι - A + 1) → Fin 2 × Fin (A - k))
    (hminor : minorPolynomial
      (stacked p x u v (A - k) (Fintype.card ι - A)) rows ≠ 0) :
    (Finset.univ.filter (fun γ => Decodable x u v k (Fintype.card ι - A) γ)).card ≤
      p * (Fintype.card ι - A + 1) := by
  classical
  exact (full_rank_Aclose_count p x hx hfixed u v k A hkA hAn rows hminor).trans
    (minor_natDegree_le p hp x u v (A - k) (Fintype.card ι - A) rows)

end
end FrobeniusLocator
end PackSource_MinorDegree

section PackSource_CofactorLine
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.CofactorLine
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {R c : Type*} [CommRing R] [Fintype c] [DecidableEq c]

/-- Add one free column to a square pivot block. -/
def bordered (A : Matrix c c R) (b : c → R) : Matrix c (Option c) R :=
  fun i j => match j with | none => b i | some j => A i j

/-- Signed maximal cofactors, represented by Cramer's rule. -/
def vector (A : Matrix c c R) (b : c → R) : Option c → R :=
  fun j => match j with | none => A.det | some j => -(A.cramer b j)

theorem mulVec_border (A : Matrix c c R) (b : c → R) (E : Option c → R) :
    (bordered A b).mulVec E = A.mulVec (fun j => E (some j)) + E none • b := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, bordered,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The cofactor vector annihilates every selected row, as a polynomial identity. -/
theorem annihilates (A : Matrix c c R) (b : c → R) :
    (bordered A b).mulVec (vector A b) = 0 := by
  rw [mulVec_border]
  change A.mulVec (-(A.cramer b)) + A.det • b = 0
  rw [Matrix.mulVec_neg, Matrix.mulVec_cramer]
  exact neg_add_cancel _

theorem vector_ne_zero (A : Matrix c c R) (b : c → R) (hA : A.det ≠ 0) :
    vector A b ≠ 0 := by
  intro h
  exact hA (congrFun h none)

/-- Cramer's cofactors commute with coefficient embeddings and evaluation. -/
theorem map_vector {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix c c R) (b : c → R) (j : Option c) :
    vector (A.map φ) (φ ∘ b) j = φ (vector A b j) := by
  cases j with
  | none => exact (φ.map_det A).symm
  | some j =>
    change -((A.map φ).cramer (φ ∘ b) j) = φ (-(A.cramer b j))
    rw [map_neg, Matrix.cramer_apply, Matrix.cramer_apply]
    congr 1
    rw [← Matrix.map_updateCol]
    exact (φ.map_det _).symm

theorem cramer_mulVec (A : Matrix c c R) (v : c → R) :
    A.cramer (A.mulVec v) = A.det • v := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem map_cramer {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix c c R) (b : c → R) (j : c) :
    (A.map φ).cramer (φ ∘ b) j = φ (A.cramer b j) := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, ← Matrix.map_updateCol]
  exact (φ.map_det _).symm

section Field
variable {K : Type*} [Field K]

/-- An invertible pivot block leaves at most one free kernel coordinate. -/
theorem kernel_zero_of_free_zero (A : Matrix c c K) (b : c → K) (hA : A.det ≠ 0)
    (E : Option c → K) (hE : (bordered A b).mulVec E = 0) (hfree : E none = 0) :
    E = 0 := by
  rw [mulVec_border, hfree, zero_smul, add_zero] at hE
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hA hE
  funext j
  cases j with
  | none => exact hfree
  | some j => exact congrFun hz j

/-- Every kernel vector is the explicit cofactor vector times its free coordinate. -/
theorem kernel_line (A : Matrix c c K) (b : c → K) (hA : A.det ≠ 0)
    (E : Option c → K) (hE : (bordered A b).mulVec E = 0) :
    E = (E none / A.det) • vector A b := by
  have hz : (bordered A b).mulVec (E - (E none / A.det) • vector A b) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hE, annihilates, smul_zero, sub_zero]
  have hfree : (E - (E none / A.det) • vector A b) none = 0 := by
    change E none - (E none / A.det) * A.det = 0
    rw [div_mul_cancel₀ _ hA, sub_self]
  have heq := kernel_zero_of_free_zero A b hA _ hz hfree
  exact sub_eq_zero.mp heq

variable {row : Type*}

def pivot (M : Matrix row (Option c) K) (rows : c → row) : Matrix c c K :=
  fun i j => M (rows i) (some j)

def freeColumn (M : Matrix row (Option c) K) (rows : c → row) : c → K :=
  fun i => M (rows i) none

theorem selected_rows (M : Matrix row (Option c) K) (rows : c → row) :
    M.submatrix rows id = bordered (pivot M rows) (freeColumn M rows) := by
  ext i j
  cases j <;> rfl

/-- A single nonzero generic kernel vector forces the cofactor kernel of
the selected rows to annihilate the entire matrix. No normal-fiber rank
assertion is being assumed in this step. -/
theorem annihilates_all (M : Matrix row (Option c) K) (rows : c → row)
    (hA : (pivot M rows).det ≠ 0) (E : Option c → K) (hE0 : E ≠ 0)
    (hE : M.mulVec E = 0) :
    M.mulVec (vector (pivot M rows) (freeColumn M rows)) = 0 := by
  have hselected : (bordered (pivot M rows) (freeColumn M rows)).mulVec E = 0 := by
    rw [← selected_rows]
    funext i
    exact congrFun hE (rows i)
  have heq := kernel_line (pivot M rows) (freeColumn M rows) hA E hselected
  have hscalar : E none / (pivot M rows).det ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at heq
    exact hE0 heq
  rw [heq, Matrix.mulVec_smul] at hE
  funext i
  have h := congrFun hE i
  change (E none / (pivot M rows).det) * _ = 0 at h
  exact (mul_eq_zero.mp h).resolve_left hscalar

/-- Once the cofactor identity holds for all rows, the selected pivot
minor alone certifies the entire kernel line. -/
theorem full_kernel_line (M : Matrix row (Option c) K) (rows : c → row)
    (hA : (pivot M rows).det ≠ 0) (E : Option c → K)
    (hE : M.mulVec E = 0) :
    E = (E none / (pivot M rows).det) • vector (pivot M rows) (freeColumn M rows) := by
  apply kernel_line _ _ hA
  rw [← selected_rows]
  funext i
  exact congrFun hE (rows i)
end Field

section Polynomial
variable {F : Type*} [Field F]

/-- The cofactor height uses the sum of row degrees, including a
replacement column, rather than rank times the largest row degree. -/
theorem vector_natDegree_le (A : Matrix c c F[X]) (b : c → F[X])
    (d : c → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ d i)
    (hb : ∀ i, (b i).natDegree ≤ d i) (j : Option c) :
    (vector A b j).natDegree ≤ ∑ i, d i := by
  cases j with
  | none => exact FrobeniusLocator.natDegree_det_le_row_sum A d hA
  | some j =>
    change (-(A.cramer b j)).natDegree ≤ _
    rw [natDegree_neg, Matrix.cramer_apply]
    apply FrobeniusLocator.natDegree_det_le_row_sum _ d
    intro i k
    by_cases hkj : k = j
    · subst k
      simpa only [Matrix.updateCol_self] using hb i
    · simpa only [Matrix.updateCol_ne hkj] using hA i k

end Polynomial
end
end FrobeniusLocator.CofactorLine
end PackSource_CofactorLine

section PackSource_CofactorSpecialization
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.CofactorLine
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row c : Type*} [Field F] [Field K] [Fintype c] [DecidableEq c]

/-- Transfer a generic kernel vector through an injective coefficient
embedding. The resulting cofactor identity is polynomial and hence valid
at every specialization, including rank-drop fibers. -/
theorem polynomial_annihilates_all (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row (Option c) F[X]) (rows : c → row)
    (A : Matrix c c F[X]) (b : c → F[X])
    (hselected : M.submatrix rows id = bordered A b) (hA : A.det ≠ 0)
    (E : Option c → K) (hE0 : E ≠ 0) (hE : (M.map φ).mulVec E = 0) :
    M.mulVec (vector A b) = 0 := by
  have hmap := φ.map_det A
  rw [RingHom.mapMatrix_apply] at hmap
  have hdet : (A.map φ).det ≠ 0 := by
    rw [← hmap]
    exact fun h => hA (hφ (h.trans (map_zero φ).symm))
  have hselectedE : (bordered (A.map φ) (φ ∘ b)).mulVec E = 0 := by
    have heq : (M.map φ).submatrix rows id = bordered (A.map φ) (φ ∘ b) := by
      ext i j
      have h := congrFun (congrFun hselected i) j
      cases j <;> exact congrArg φ h
    rw [← heq]
    funext i
    exact congrFun hE (rows i)
  have hline := kernel_line (A.map φ) (φ ∘ b) hdet E hselectedE
  have hscalar : E none / (A.map φ).det ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hline
    exact hE0 hline
  have hfull : (M.map φ).mulVec (vector (A.map φ) (φ ∘ b)) = 0 := by
    rw [hline, Matrix.mulVec_smul] at hE
    funext i
    have h := congrFun hE i
    change (E none / (A.map φ).det) * _ = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hscalar
  funext i
  apply hφ
  change φ ((M.mulVec (vector A b)) i) = φ (0 : F[X])
  rw [map_zero]
  have hi := congrFun hfull i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi ⊢
  rw [map_sum]
  simp only [map_mul]
  simpa only [map_vector, Pi.zero_apply] using hi

/-- One nonzero pivot determinant controls every regular specialized
kernel. Its zeros are the only fibers for which this equality is omitted. -/
theorem specialized_kernel_line (M : Matrix row (Option c) F[X]) (rows : c → row)
    (A : Matrix c c F[X]) (b : c → F[X])
    (hselected : M.submatrix rows id = bordered A b)
    (γ : F) (hγ : A.det.eval γ ≠ 0) (E : Option c → F)
    (hE : (M.map (evalRingHom γ)).mulVec E = 0) :
    E = (E none / A.det.eval γ) • (fun j => (vector A b j).eval γ) := by
  let φ := evalRingHom γ
  have hmap := φ.map_det A
  rw [RingHom.mapMatrix_apply] at hmap
  have hdet : (A.map φ).det ≠ 0 := by
    rw [← hmap]
    exact hγ
  have hselectedE : (bordered (A.map φ) (φ ∘ b)).mulVec E = 0 := by
    have heq : (M.map φ).submatrix rows id = bordered (A.map φ) (φ ∘ b) := by
      ext i j
      have h := congrFun (congrFun hselected i) j
      cases j <;> exact congrArg φ h
    rw [← heq]
    funext i
    exact congrFun hE (rows i)
  have h := kernel_line (A.map φ) (φ ∘ b) hdet E hselectedE
  have heq : vector (A.map φ) (φ ∘ b) = fun j => (vector A b j).eval γ :=
    funext (map_vector φ A b)
  rw [heq, ← hmap] at h
  exact h

end
end FrobeniusLocator.CofactorLine
end PackSource_CofactorSpecialization

section PackSource_GenericRank
set_option autoImplicit true
namespace FrobeniusLocator.GenericRank
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The row-minor extraction used by the probe, proved here with only
Mathlib dependencies rather than importing the old geometric proof tree. -/
theorem exists_rows_det_ne_zero {row : Type*} [Fintype row] {m : ℕ} (A : Matrix row (Fin m) K)
    (hker : ∀ v, A.mulVec v = 0 → v = 0) :
    ∃ rows : Fin m → row, (A.submatrix rows id).det ≠ 0 := by
  have hk : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hker v (by simpa only [Matrix.mulVecLin_apply] using hv)
  have hr : A.rank = m := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hk, finrank_bot, add_zero, Module.finrank_fin_fun] at h
    exact h
  rw [Matrix.rank_eq_finrank_span_row] at hr
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = m := by
    rw [← finrank_span_eq_card hli, hsp, hr]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent K (A.submatrix (a ∘ e) id).row := by
    have heq : (A.submatrix (a ∘ e) id).row = (A.row ∘ a) ∘ e := by
      funext i j
      rfl
    rw [heq]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli')).ne_zero

/-- A one-dimensional kernel with nonzero free coordinate supplies the
required square pivot minor; its existence is not left as a hypothesis. -/
theorem exists_pivot_of_kernel_line {row : Type*} [Fintype row] {m : ℕ} (M : Matrix row (Option (Fin m)) K)
    (E : Option (Fin m) → K) (hfree : E none ≠ 0)
    (hline : ∀ v, M.mulVec v = 0 → ∃ a : K, v = a • E) :
    ∃ rows : Fin m → row, (CofactorLine.pivot M rows).det ≠ 0 := by
  let A : Matrix row (Fin m) K := fun i j => M i (some j)
  obtain ⟨rows, hrows⟩ := exists_rows_det_ne_zero A (by
    intro v hv
    let v' : Option (Fin m) → K := fun j => match j with | none => 0 | some j => v j
    have hv' : M.mulVec v' = 0 := by
      funext i
      change (∑ j : Option (Fin m), M i j * v' j) = 0
      rw [Fintype.sum_option]
      simpa only [v', mul_zero, add_zero, zero_add, A, Matrix.mulVec, dotProduct,
        Pi.zero_apply] using congrFun hv i
    obtain ⟨a, ha⟩ := hline v' hv'
    have hscalar : a = 0 := by
      have h := congrFun ha none
      change 0 = a * E none at h
      exact (mul_eq_zero.mp h.symm).resolve_right hfree
    funext j
    have h := congrFun ha (some j)
    simpa only [v', hscalar, zero_smul, Pi.zero_apply] using h)
  exact ⟨rows, hrows⟩

/-- A one-dimensional finite kernel is spanned by any one of its
nonzero vectors. This avoids an implicit choice of a rational basis. -/
theorem kernel_line_of_finrank {row col : Type*} [Fintype col]
    (M : Matrix row col K) (hnull : Module.finrank K (LinearMap.ker M.mulVecLin) = 1)
    (E : col → K) (hE : E ≠ 0) (hME : M.mulVec E = 0) :
    ∀ v, M.mulVec v = 0 → ∃ a : K, v = a • E := by
  have hspan : K ∙ E = LinearMap.ker M.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact hME
    · rw [finrank_span_singleton hE, hnull]
  intro v hv
  have hmem : v ∈ K ∙ E := by rw [hspan]; exact hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨a, ha.symm⟩

theorem nullity_one_of_rank {row col : Type*} [Fintype col]
    (M : Matrix row col K) (hr : M.rank + 1 = Fintype.card col) :
    Module.finrank K (LinearMap.ker M.mulVecLin) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  change M.rank + _ = _ at h
  omega

end
end FrobeniusLocator.GenericRank
end PackSource_GenericRank

section PackSource_NormalFiber
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]

/-- Concrete data sufficient to specialize a generic row space. The
nonzero pivot minor is also the exceptional polynomial used for counting. -/
structure RowBasis (φ : F[X] →+* K) (M : Matrix row col F[X]) (r : ℕ) where
  rows : Fin r → row
  cols : Fin r → col
  minor_ne : (M.submatrix rows cols).det ≠ 0
  spans : ∀ i, ∃ a : Fin r → K, ∀ j,
    φ (M i j) = ∑ q, a q * φ (M (rows q) j)

def pivot {r : ℕ} {φ : F[X] →+* K} {M : Matrix row col F[X]}
    (B : RowBasis φ M r) : Matrix (Fin r) (Fin r) F[X] := M.submatrix B.rows B.cols

def rowCoefficients {r : ℕ} {φ : F[X] →+* K} {M : Matrix row col F[X]}
    (B : RowBasis φ M r) (i : row) : Fin r → F[X] :=
  (pivot B).transpose.cramer (fun q => M i (B.cols q))

/-- Clear denominators using one pivot determinant. The relation is a
polynomial identity, not an assertion valid only at sampled slopes. -/
theorem row_relation (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r) (i : row) (j : col) :
    (pivot B).det * M i j = ∑ q, rowCoefficients B i q * M (B.rows q) j := by
  obtain ⟨a, ha⟩ := B.spans i
  let A := (pivot B).map φ
  have hsolve : A.transpose.mulVec a = fun q => φ (M i (B.cols q)) := by
    funext q
    change (∑ l, φ (M (B.rows l) (B.cols q)) * a l) = _
    simpa only [mul_comm] using (ha (B.cols q)).symm
  have hc : ∀ q, φ (rowCoefficients B i q) = φ (pivot B).det * a q := by
    intro q
    have hm := CofactorLine.map_cramer φ (pivot B).transpose
      (fun q => M i (B.cols q)) q
    have hcr := congrFun (CofactorLine.cramer_mulVec A.transpose a) q
    rw [hsolve, Matrix.det_transpose] at hcr
    have hd := φ.map_det (pivot B)
    rw [RingHom.mapMatrix_apply] at hd
    change φ (rowCoefficients B i q) = _
    calc
      _ = ((pivot B).transpose.map φ).cramer (fun q => φ (M i (B.cols q))) q := hm.symm
      _ = A.det * a q := hcr
      _ = _ := by rw [← hd]
  apply hφ
  rw [map_mul, map_sum]
  simp only [map_mul, hc]
  rw [ha j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Outside the chosen pivot minor, the specialized row space equals
the specialized generic row basis. This is the normal-fiber API used by
all low-nullity, constant-kernel, and pruning applications. -/
theorem kernel_eq_selected (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r)
    (γ : F) (hγ : (pivot B).det.eval γ ≠ 0) (v : col → F) :
    (M.map (evalRingHom γ)).mulVec v = 0 ↔
      ((M.submatrix B.rows id).map (evalRingHom γ)).mulVec v = 0 := by
  constructor
  · intro h
    funext i
    exact congrFun h (B.rows i)
  · intro h
    funext i
    apply (mul_eq_zero.mp (show (pivot B).det.eval γ *
      ((M.map (evalRingHom γ)).mulVec v) i = 0 from ?_)).resolve_left hγ
    have heval : ∀ j, (pivot B).det.eval γ * (M i j).eval γ =
        ∑ q, (rowCoefficients B i q).eval γ * (M (B.rows q) j).eval γ := by
      intro j
      have hrel := congrArg (evalRingHom γ) (row_relation φ hφ M r B i j)
      simp only [map_mul, map_sum] at hrel
      exact hrel
    change (pivot B).det.eval γ * (∑ j, (M i j).eval γ * v j) = 0
    rw [Finset.mul_sum]
    simp_rw [← mul_assoc, heval, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q hq
    have hz := congrFun h q
    change (∑ j, (M (B.rows q) j).eval γ * v j) = 0 at hz
    calc
      _ = (rowCoefficients B i q).eval γ * (∑ j, (M (B.rows q) j).eval γ * v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hz, mul_zero]

/-- Every finite generic matrix has a row-space basis and a nonzero
square pivot minor. Consequently normal-fiber specialization is obtained
from a rank hypothesis rather than assumed as an extra theorem. -/
theorem exists_rowBasis [Fintype row] (φ : F[X] →+* K) (M : Matrix row col F[X])
    (r : ℕ) (hr : (M.map φ).rank = r) : Nonempty (RowBasis φ M r) := by
  classical
  let N := M.map φ
  have hr' : Module.finrank K (Submodule.span K (Set.range N.row)) = r := by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hr
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K N.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hsp, hr']
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  let rows := a ∘ e
  have hli' : LinearIndependent K (fun q : Fin r => N.row (rows q)) :=
    hli.comp e e.injective
  have hspace : Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) =
      Submodule.span K (Set.range N.row) := by
    rw [← hsp]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      exact ⟨e q, rfl⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨l, hl⟩ := e.surjective q
      exact ⟨l, by simp only [rows, Function.comp_apply, hl]⟩
  let T := N.submatrix rows id
  obtain ⟨cols, hcols⟩ := GenericRank.exists_rows_det_ne_zero T.transpose (by
    intro v hv
    have hsum : (∑ q, v q • N.row (rows q)) = 0 := by
      funext j
      have h := congrFun hv j
      change (∑ q, N (rows q) j * v q) = 0 at h
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        Matrix.row, Pi.zero_apply] using h
    funext q
    exact Fintype.linearIndependent_iff.mp hli' v hsum q)
  have hminorK : (N.submatrix rows cols).det ≠ 0 := by
    have heq : T.transpose.submatrix cols id = (N.submatrix rows cols).transpose := by
      ext i j
      rfl
    rw [heq, Matrix.det_transpose] at hcols
    exact hcols
  refine ⟨⟨rows, cols, ?_, ?_⟩⟩
  · intro hzero
    apply hminorK
    have hmap := φ.map_det (M.submatrix rows cols)
    rw [RingHom.mapMatrix_apply, hzero, map_zero] at hmap
    exact hmap.symm
  · intro i
    have hmem : N.row i ∈ Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) := by
      rw [hspace]
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    refine ⟨v, ?_⟩
    intro j
    have h := congrFun hv j
    simpa only [N, Matrix.row, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm

/-- The chosen generic rank is exactly preserved outside its pivot
minor. This proves the nullity assertion used in the counting arguments. -/
theorem rank_specializes [Fintype row] (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r)
    (γ : F) (hγ : (pivot B).det.eval γ ≠ 0) :
    (M.map (evalRingHom γ)).rank = r := by
  let N := M.map (evalRingHom γ)
  let T := (M.submatrix B.rows id).map (evalRingHom γ)
  change N.rank = r
  have hminor : (N.submatrix B.rows B.cols).det ≠ 0 := by
    have hmap := (evalRingHom γ).map_det (pivot B)
    rw [RingHom.mapMatrix_apply] at hmap
    intro h0
    apply hγ
    have heq : N.submatrix B.rows B.cols = (pivot B).map (evalRingHom γ) := rfl
    rw [heq, ← hmap] at h0
    exact h0
  have hTrank : T.rank = r := by
    have hminorRank := Matrix.rank_of_det_ne_zero hminor
    have hlo := Matrix.rank_submatrix_le T id B.cols
    have hhi := Matrix.rank_le_card_height T
    change (N.submatrix B.rows B.cols).rank ≤ T.rank at hlo
    rw [hminorRank, Fintype.card_fin] at hlo
    rw [Fintype.card_fin] at hhi
    omega
  have hker : LinearMap.ker N.mulVecLin = LinearMap.ker T.mulVecLin := by
    ext v
    exact kernel_eq_selected φ hφ M r B γ hγ v
  have hN := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have hT := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
  change N.rank + Module.finrank F (LinearMap.ker N.mulVecLin) = _ at hN
  change T.rank + Module.finrank F (LinearMap.ker T.mulVecLin) = _ at hT
  rw [hker] at hN
  rw [hTrank] at hT
  omega

/-- A constant subspace with the generic nullity and contained in all
fibers is the full normal kernel. This establishes the mathematical
constant-kernel criterion from finite-dimensional data. -/
theorem constant_kernel_eq_normal [Fintype row] (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r)
    (V : Submodule F (col → F)) (hV : Module.finrank F V = Fintype.card col - r)
    (hsub : ∀ γ v, v ∈ V → (M.map (evalRingHom γ)).mulVec v = 0)
    (γ : F) (hγ : (pivot B).det.eval γ ≠ 0) :
    LinearMap.ker (M.map (evalRingHom γ)).mulVecLin = V := by
  have hrank := rank_specializes φ hφ M r B γ hγ
  have hn := LinearMap.finrank_range_add_finrank_ker (M.map (evalRingHom γ)).mulVecLin
  change (M.map (evalRingHom γ)).rank + _ = _ at hn
  rw [hrank, Module.finrank_fintype_fun_eq_card] at hn
  have hdim : Module.finrank F (LinearMap.ker (M.map (evalRingHom γ)).mulVecLin) = Fintype.card col - r := by omega
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv
    exact hsub γ v hv
  · rw [hV, hdim]

theorem minor_degree_le (φ : F[X] →+* K) (M : Matrix row col F[X]) (r : ℕ)
    (B : RowBasis φ M r) (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) :
    (pivot B).det.natDegree ≤ ∑ q, d (B.rows q) := by
  exact FrobeniusLocator.natDegree_det_le_row_sum _ _
    (fun i j => hdeg (B.rows i) (B.cols j))

end
end FrobeniusLocator.NormalFiber
end PackSource_NormalFiber

section PackSource_GenericCofactor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace FrobeniusLocator.GenericCofactor
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators

section Ring
variable {R row col : Type*} [CommRing R] [Fintype col] [DecidableEq col]
variable {r : ℕ}

/-- The coordinate inclusion of the selected pivot columns. -/
def inclusion (cols : Fin r → col) : Matrix col (Fin r) R :=
  fun j q => (Pi.single (cols q) (1 : R) : col → R) j

theorem selected_mul_inclusion (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) :
    M.submatrix rows id * inclusion cols = M.submatrix rows cols := by
  ext i q
  change (M.submatrix rows id).mulVec (Pi.single (cols q) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

/-- A denominator-cleared projection onto the kernel of selected rows. -/
def cofactorMap (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col) :
    (col → R) →ₗ[R] (col → R) :=
  (M.submatrix rows cols).det • LinearMap.id -
    (inclusion cols).mulVecLin.comp
      ((M.submatrix rows cols).cramer.comp (M.submatrix rows id).mulVecLin)

/-- One polynomial cofactor vector per column. Pivot columns give zero
vectors; redundant indexing avoids imposing a new enumeration on clients. -/
def rawVector (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col)
    (j : col) : col → R := cofactorMap M rows cols (Pi.single j 1)

theorem cofactorMap_apply (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R) :
    cofactorMap M rows cols v = (M.submatrix rows cols).det • v -
      (inclusion cols).mulVec ((M.submatrix rows cols).cramer
        ((M.submatrix rows id).mulVec v)) := rfl

theorem rawVector_apply (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (j : col) :
    rawVector M rows cols j = (M.submatrix rows cols).det • Pi.single j 1 -
      (inclusion cols).mulVec ((M.submatrix rows cols).cramer
        (fun q => M (rows q) j)) := by
  rw [rawVector, cofactorMap_apply, Matrix.mulVec_single_one]
  rfl

theorem selected_annihilates_map (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R) :
    (M.submatrix rows id).mulVec (cofactorMap M rows cols v) = 0 := by
  rw [cofactorMap_apply, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, selected_mul_inclusion, Matrix.mulVec_cramer, sub_self]

theorem selected_annihilates (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (j : col) :
    (M.submatrix rows id).mulVec (rawVector M rows cols j) = 0 :=
  selected_annihilates_map M rows cols _

theorem cofactorMap_of_kernel (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R)
    (hv : (M.submatrix rows id).mulVec v = 0) :
    cofactorMap M rows cols v = (M.submatrix rows cols).det • v := by
  rw [cofactorMap_apply, hv, map_zero, Matrix.mulVec_zero, sub_zero]

theorem sum_rawVector (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R) :
    ∑ j, v j • rawVector M rows cols j = cofactorMap M rows cols v := by
  simp only [rawVector, ← map_smul, ← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]

theorem map_rawVector {S : Type*} [CommRing S] (ψ : R →+* S)
    (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col) (j c : col) :
    rawVector (M.map ψ) rows cols j c = ψ (rawVector M rows cols j c) := by
  have hsub : (M.map ψ).submatrix rows cols = (M.submatrix rows cols).map ψ := rfl
  have hd := ψ.map_det (M.submatrix rows cols)
  rw [RingHom.mapMatrix_apply] at hd
  have hc : ((M.submatrix rows cols).map ψ).cramer
      (fun q => ψ (M (rows q) j)) =
      fun q => ψ ((M.submatrix rows cols).cramer (fun q => M (rows q) j) q) := by
    funext q
    exact CofactorLine.map_cramer ψ _ _ q
  have hs : ∀ a : col, ψ ((Pi.single a (1 : R) : col → R) c) =
      (Pi.single a (1 : S) : col → S) c := by
    intro a
    by_cases h : a = c <;> simp [h]
  simp only [rawVector_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsub, ← hd, map_sub, map_mul, hs]
  congr 1
  change (∑ q, (Pi.single (cols q) (1 : S) : col → S) c *
      ((M.submatrix rows cols).map ψ).cramer (fun q => ψ (M (rows q) j)) q) = _
  rw [hc]
  simp only [Matrix.mulVec, dotProduct, inclusion, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hs]

end Ring

section Field
variable {K row col : Type*} [Field K] [Fintype col] [DecidableEq col]
variable {r : ℕ}

theorem raw_spans (M : Matrix row col K) (rows : Fin r → row) (cols : Fin r → col)
    (hdet : (M.submatrix rows cols).det ≠ 0) (v : col → K)
    (hv : (M.submatrix rows id).mulVec v = 0) :
    v = ∑ j, (v j / (M.submatrix rows cols).det) • rawVector M rows cols j := by
  have heq := sum_rawVector M rows cols v
  rw [cofactorMap_of_kernel _ _ _ _ hv] at heq
  calc
    v = (M.submatrix rows cols).det⁻¹ • ((M.submatrix rows cols).det • v) := by
      rw [smul_smul, inv_mul_cancel₀ hdet, one_smul]
    _ = _ := by
      rw [← heq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul, div_eq_mul_inv, mul_comm]

end Field

section Polynomial
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}

def vector (B : NormalFiber.RowBasis φ M r) (j : col) : col → F[X] :=
  rawVector M B.rows B.cols j

/-- Generic row spanning is enough to recover the entire kernel from
the selected rows over the fraction field. -/
theorem generic_kernel_eq_selected (B : NormalFiber.RowBasis φ M r) (v : col → K) :
    (M.map φ).mulVec v = 0 ↔ ((M.submatrix B.rows id).map φ).mulVec v = 0 := by
  constructor
  · intro h
    funext q
    exact congrFun h (B.rows q)
  · intro h
    funext i
    obtain ⟨a, ha⟩ := B.spans i
    change (∑ j, φ (M i j) * v j) = 0
    simp_rw [ha, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q hq
    have hz := congrFun h q
    change (∑ j, φ (M (B.rows q) j) * v j) = 0 at hz
    calc
      _ = a q * (∑ j, φ (M (B.rows q) j) * v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hz, mul_zero]

theorem annihilates (B : NormalFiber.RowBasis φ M r) (hφ : Function.Injective φ)
    (j : col) : M.mulVec (vector B j) = 0 := by
  have hsel := selected_annihilates (M.map φ) B.rows B.cols j
  have hfull := (generic_kernel_eq_selected B _).mpr hsel
  funext i
  apply hφ
  have h := congrFun hfull i
  simpa only [vector, Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
    Matrix.map_apply, map_rawVector, Pi.zero_apply] using h

theorem generic_spans (B : NormalFiber.RowBasis φ M r) (hφ : Function.Injective φ)
    (v : col → K) (hv : (M.map φ).mulVec v = 0) :
    v = ∑ j, (v j / φ (NormalFiber.pivot B).det) •
      (fun c => φ (vector B j c)) := by
  have hd := φ.map_det (NormalFiber.pivot B)
  rw [RingHom.mapMatrix_apply] at hd
  have hd' : φ (NormalFiber.pivot B).det =
      ((M.map φ).submatrix B.rows B.cols).det := hd
  have hdet : ((M.map φ).submatrix B.rows B.cols).det ≠ 0 := by
    rw [← hd']
    exact fun h => B.minor_ne (hφ (h.trans (map_zero φ).symm))
  have hsel := (generic_kernel_eq_selected B v).mp hv
  have heq := raw_spans (M.map φ) B.rows B.cols hdet v hsel
  have hmap : ∀ j, rawVector (M.map φ) B.rows B.cols j =
      fun c => φ (vector B j c) := fun j => funext (map_rawVector φ M B.rows B.cols j)
  simpa only [← hd', hmap] using heq

theorem vector_natDegree_le (B : NormalFiber.RowBasis φ M r)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) (j c : col) :
    (vector B j c).natDegree ≤ ∑ q, d (B.rows q) := by
  classical
  rw [vector, rawVector_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · by_cases hj : j = c
    · subst c
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one,
        NormalFiber.pivot] using
        NormalFiber.minor_degree_le φ M r B d hdeg
    · simp [Pi.smul_apply, Pi.single_apply, hj]
  · change (∑ q, inclusion B.cols c q *
      (M.submatrix B.rows B.cols).cramer (fun q => M (B.rows q) j) q).natDegree ≤ _
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    by_cases hq : B.cols q = c
    · simp only [inclusion, hq, Pi.single_eq_same, one_mul, Matrix.cramer_apply]
      apply FrobeniusLocator.natDegree_det_le_row_sum _ (fun q => d (B.rows q))
      intro i k
      by_cases hk : k = q
      · subst k
        simpa only [Matrix.updateCol_self] using hdeg (B.rows i) j
      · simpa only [Matrix.updateCol_ne hk, Matrix.submatrix_apply] using
          hdeg (B.rows i) (B.cols k)
    · simp [inclusion, Pi.single_apply, hq]

theorem specialized_spans (B : NormalFiber.RowBasis φ M r)
    (γ : F) (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0) (v : col → F)
    (hv : (M.map (evalRingHom γ)).mulVec v = 0) :
    v = ∑ j, (v j / (NormalFiber.pivot B).det.eval γ) •
      (fun c => (vector B j c).eval γ) := by
  let ψ := evalRingHom γ
  have hsel : ((M.map ψ).submatrix B.rows id).mulVec v = 0 := by
    funext q
    exact congrFun hv (B.rows q)
  have heq := sum_rawVector (M.map ψ) B.rows B.cols v
  rw [cofactorMap_of_kernel _ _ _ _ hsel] at heq
  have hd := ψ.map_det (NormalFiber.pivot B)
  rw [RingHom.mapMatrix_apply] at hd
  have hd' : ((M.map ψ).submatrix B.rows B.cols).det =
      (NormalFiber.pivot B).det.eval γ := hd.symm
  rw [hd'] at heq
  have hmap : ∀ j, rawVector (M.map ψ) B.rows B.cols j =
      fun c => (vector B j c).eval γ := fun j => funext (map_rawVector ψ M B.rows B.cols j)
  simp_rw [hmap] at heq
  calc
    v = ((NormalFiber.pivot B).det.eval γ)⁻¹ •
        ((NormalFiber.pivot B).det.eval γ • v) := by
      rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
    _ = _ := by
      rw [← heq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem eval_annihilates (B : NormalFiber.RowBasis φ M r) (hφ : Function.Injective φ)
    (γ : F) (j : col) :
    (M.map (evalRingHom γ)).mulVec (fun c => (vector B j c).eval γ) = 0 := by
  funext i
  have h := congrArg (evalRingHom γ) (congrFun (annihilates B hφ j) i)
  simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
    Matrix.map_apply, Matrix.mulVecLin_apply, Polynomial.coe_evalRingHom, Pi.zero_apply] using h

/-- Equality of the normal kernel with evaluations of bounded polynomial
cofactors. No rational-function evaluation is involved. -/
theorem normal_kernel_eq_span (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (γ : F)
    (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0) :
    LinearMap.ker (M.map (evalRingHom γ)).mulVecLin =
      Submodule.span F (Set.range (fun j c => (vector B j c).eval γ)) := by
  apply le_antisymm
  · intro v hv
    rw [specialized_spans B γ hγ v hv]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self j)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact eval_annihilates B hφ γ j

/-- The same normal kernel is obtained by evaluating all polynomial
kernel sections. This is the literal specialization-of-kernel statement. -/
theorem normal_kernel_eq_polynomial_sections (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (γ : F)
    (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0) :
    LinearMap.ker (M.map (evalRingHom γ)).mulVecLin =
      Submodule.span F
        {v | ∃ P : col → F[X], M.mulVec P = 0 ∧ v = fun c => (P c).eval γ} := by
  apply le_antisymm
  · rw [normal_kernel_eq_span B hφ γ hγ]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨vector B j, annihilates B hφ j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨P, hP, rfl⟩
    funext i
    have h := congrArg (evalRingHom γ) (congrFun hP i)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
      Matrix.map_apply, Matrix.mulVecLin_apply, Polynomial.coe_evalRingHom, Pi.zero_apply] using h

/-- Every vector of a normal fiber has an actual polynomial kernel
lift, with the SAME coordinate-degree ledger as the cofactors. -/
theorem normal_polynomial_lift (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (d : row → ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d i)
    (γ : F) (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0)
    (v : col → F) (hv : (M.map (evalRingHom γ)).mulVec v = 0) :
    ∃ P : col → F[X], M.mulVec P = 0 ∧
      (∀ c, (P c).eval γ = v c) ∧
      (∀ c, (P c).natDegree ≤ ∑ q, d (B.rows q)) := by
  let a : col → F := fun j => v j / (NormalFiber.pivot B).det.eval γ
  let P : col → F[X] := ∑ j, C (a j) • vector B j
  refine ⟨P, ?_, ?_, ?_⟩
  · dsimp only [P]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, annihilates B hφ, smul_zero, Finset.sum_const_zero]
  · intro c
    have heq := congrFun (specialized_spans B γ hγ v hv) c
    simpa only [P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      eval_finsetSum, eval_mul, eval_C, a] using heq.symm
  · intro c
    simp only [P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact Polynomial.natDegree_mul_le.trans (by
      simpa only [natDegree_C, zero_add] using vector_natDegree_le B d hdeg j c)

/-- A row functional vanishing on every generic kernel vector also
vanishes on every normal specialized kernel vector. This is the common-
node restriction transport needed at pruning's terminal step. -/
theorem common_functional_specializes (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (a : col → F[X])
    (ha : ∀ v : col → K, (M.map φ).mulVec v = 0 →
      ∑ c, φ (a c) * v c = 0)
    (γ : F) (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0)
    (v : col → F) (hv : (M.map (evalRingHom γ)).mulVec v = 0) :
    ∑ c, (a c).eval γ * v c = 0 := by
  have hz : ∀ j, ∑ c, a c * vector B j c = 0 := by
    intro j
    apply hφ
    rw [map_sum, map_zero]
    simp only [map_mul]
    apply ha
    funext i
    have h := congrArg φ (congrFun (annihilates B hφ j) i)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
      Matrix.map_apply, Matrix.mulVecLin_apply, Polynomial.coe_evalRingHom, Pi.zero_apply] using h
  have hze : ∀ j, ∑ c, (a c).eval γ * (vector B j c).eval γ = 0 := by
    intro j
    have h := congrArg (evalRingHom γ) (hz j)
    simpa only [map_sum, map_mul, map_zero, Polynomial.coe_evalRingHom] using h
  rw [specialized_spans B γ hγ v hv]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    _ = (v j / (NormalFiber.pivot B).det.eval γ) *
        (∑ c, (a c).eval γ * (vector B j c).eval γ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = 0 := by rw [hze, mul_zero]

end Polynomial
end
end FrobeniusLocator.GenericCofactor
end PackSource_GenericCofactor

section PackSource_AppendConstants
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.AppendConstants
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators

variable {F row extra col : Type*} [Field F] [Fintype col] [DecidableEq col]

/-- Append parameter-independent linear constraints. -/
def append (M : Matrix row col F[X]) (E : Matrix extra col F) :
    Matrix (row ⊕ extra) col F[X] :=
  Sum.elim M (fun i j => C (E i j))

def appendOver {K : Type*} [Field K] (M : Matrix row col K) (E : Matrix extra col K) :
    Matrix (row ⊕ extra) col K := Sum.elim M E

theorem appendOver_kernel {K : Type*} [Field K]
    (M : Matrix row col K) (E : Matrix extra col K) (v : col → K) :
    (appendOver M E).mulVec v = 0 ↔ M.mulVec v = 0 ∧ E.mulVec v = 0 := by
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (Sum.inl i)),
      funext (fun i => congrFun h (Sum.inr i))⟩
  · rintro ⟨hM, hE⟩
    funext i
    cases i with
    | inl i => exact congrFun hM i
    | inr i => exact congrFun hE i

theorem kernel_eval (M : Matrix row col F[X]) (E : Matrix extra col F)
    (γ : F) (v : col → F) :
    ((append M E).map (evalRingHom γ)).mulVec v = 0 ↔
      (M.map (evalRingHom γ)).mulVec v = 0 ∧ E.mulVec v = 0 := by
  have heq : (append M E).map (evalRingHom γ) =
      appendOver (M.map (evalRingHom γ)) E := by
    ext i j
    cases i <;> simp [append, appendOver]
  rw [heq]
  exact appendOver_kernel _ _ _

theorem row_degree (M : Matrix row col F[X]) (E : Matrix extra col F)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) :
    ∀ i j, (append M E i j).natDegree ≤ Sum.elim d (fun _ => 0) i := by
  intro i j
  cases i with
  | inl i => exact hdeg i j
  | inr i => simp [append]

/-- Appended node evaluations, used by pruning in coefficient space. -/
def evaluationRows {ι : Type*} (x : ι → F) (t : ℕ) : Matrix ι (Fin (t+1)) F :=
  fun i j => x i ^ j.val

theorem evaluationRows_mulVec {ι : Type*} (x : ι → F) (t : ℕ)
    (v : Fin (t+1) → F) (i : ι) :
    (evaluationRows x t).mulVec v i =
      (∑ j : Fin (t+1), monomial j.val (v j)).eval (x i) := by
  simp only [evaluationRows, Matrix.mulVec, dotProduct, eval_finset_sum,
    eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

end
end FrobeniusLocator.AppendConstants
end PackSource_AppendConstants

section PackSource_RankCertificate
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}

theorem rows_injective (B : RowBasis φ M r) : Function.Injective B.rows := by
  intro i j hij
  by_contra hne
  apply B.minor_ne
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp only [Matrix.submatrix_apply, hij]

theorem cols_injective (B : RowBasis φ M r) : Function.Injective B.cols := by
  intro i j hij
  by_contra hne
  apply B.minor_ne
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, hij])

/-- A row-basis certificate has its advertised generic rank. -/
theorem generic_rank_eq [Fintype row] (B : RowBasis φ M r) (hφ : Function.Injective φ) :
    (M.map φ).rank = r := by
  let N := M.map φ
  let T := (M.submatrix B.rows id).map φ
  change N.rank = r
  have hd := φ.map_det (pivot B)
  rw [RingHom.mapMatrix_apply] at hd
  have hminor : (N.submatrix B.rows B.cols).det ≠ 0 := by
    change ((pivot B).map φ).det ≠ 0
    rw [← hd]
    exact fun h => B.minor_ne (hφ (h.trans (map_zero φ).symm))
  have hTrank : T.rank = r := by
    have hlo := Matrix.rank_submatrix_le T id B.cols
    have hhi := Matrix.rank_le_card_height T
    change (N.submatrix B.rows B.cols).rank ≤ T.rank at hlo
    rw [Matrix.rank_of_det_ne_zero hminor, Fintype.card_fin] at hlo
    rw [Fintype.card_fin] at hhi
    omega
  have hk : LinearMap.ker N.mulVecLin = LinearMap.ker T.mulVecLin := by
    ext v
    exact GenericCofactor.generic_kernel_eq_selected B v
  have hn := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have ht := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
  change N.rank + _ = _ at hn
  change T.rank + _ = _ at ht
  rw [hk] at hn
  rw [hTrank] at ht
  omega

theorem selected_degree_sum_le [Fintype row] (B : RowBasis φ M r) (d : row → ℕ) :
    ∑ q, d (B.rows q) ≤ ∑ i, d i := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image B.rows, d i := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact rows_injective B hij
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem exceptional_card_le (B : RowBasis φ M r) (d : row → ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d i) (Γ : Finset F)
    (hΓ : ∀ γ ∈ Γ, (pivot B).det.eval γ = 0) : Γ.card ≤ ∑ q, d (B.rows q) := by
  exact (Polynomial.card_le_degree_of_subset_roots (fun γ hγ =>
    (Polynomial.mem_roots B.minor_ne).mpr (hΓ γ hγ))).trans
    (minor_degree_le φ M r B d hdeg)

end
end FrobeniusLocator.NormalFiber
end PackSource_RankCertificate

section PackSource_AppendBudget
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.AppendConstants
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row extra col : Type*} [Field F] [Field K]
  [Fintype col] [DecidableEq col] [Fintype extra]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}

def rowEmbedding (rows : Fin r → row) : Fin r ⊕ extra → row ⊕ extra :=
  Sum.map rows id

theorem append_reduced (B : NormalFiber.RowBasis φ M r) (E : Matrix extra col F) :
    (append M E).submatrix (rowEmbedding B.rows) id =
      append (M.submatrix B.rows id) E := by
  ext i j
  cases i <;> rfl

/-- A generic basis for the matrix with the old selected rows lifts to
the full augmented matrix. Constant new constraints cost no row degree. -/
theorem lift_rowBasis (B : NormalFiber.RowBasis φ M r) (E : Matrix extra col F)
    {s : ℕ} (C : NormalFiber.RowBasis φ (append (M.submatrix B.rows id) E) s) :
    ∃ B' : NormalFiber.RowBasis φ (append M E) s,
      B'.rows = rowEmbedding B.rows ∘ C.rows ∧ B'.cols = C.cols := by
  classical
  let R := append (M.submatrix B.rows id) E
  let A := append M E
  let rows := rowEmbedding B.rows ∘ C.rows
  have hred : ∀ i j, A (rowEmbedding B.rows i) j = R i j := by
    intro i j
    cases i <;> rfl
  let W := Submodule.span K (Set.range (fun q : Fin s => fun j => φ (R (C.rows q) j)))
  have hR : ∀ i, (fun j => φ (R i j)) ∈ W := by
    intro i
    obtain ⟨a, ha⟩ := C.spans i
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨a, ?_⟩
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (ha j).symm
  have hA : ∀ i, (fun j => φ (A i j)) ∈ W := by
    intro i
    cases i with
    | inl i =>
      obtain ⟨a, ha⟩ := B.spans i
      have heq : (fun j => φ (A (Sum.inl i) j)) =
          ∑ q, a q • (fun j => φ (R (Sum.inl q) j)) := by
        funext j
        simpa only [A, R, append, Sum.elim_inl, Matrix.submatrix_apply,
          id_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha j
      rw [heq]
      apply Submodule.sum_mem
      intro q hq
      exact Submodule.smul_mem W _ (hR _)
    | inr i => exact hR (Sum.inr i)
  refine ⟨⟨rows, C.cols, ?_, ?_⟩, rfl, rfl⟩
  · have heq : A.submatrix rows C.cols = R.submatrix C.rows C.cols := by
      funext i j
      exact hred _ _
    rw [heq]
    exact C.minor_ne
  · intro i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hA i)
    refine ⟨a, ?_⟩
    intro j
    have hh := congrFun ha j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    change φ (A i j) = ∑ q, a q * φ (A (rows q) j)
    simpa only [rows, Function.comp_apply, hred] using hh.symm

/-- Any number of appended constant rows admits a maximal minor whose
degree is bounded by the ORIGINAL selected-row ledger. -/
theorem exists_append_basis_budget (B : NormalFiber.RowBasis φ M r)
    (E : Matrix extra col F) (d : row → ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d i) :
    ∃ (s : ℕ) (B' : NormalFiber.RowBasis φ (append M E) s),
      (NormalFiber.pivot B').det.natDegree ≤ ∑ q, d (B.rows q) := by
  classical
  let R := append (M.submatrix B.rows id) E
  let s := (R.map φ).rank
  obtain ⟨C⟩ := NormalFiber.exists_rowBasis φ R s rfl
  obtain ⟨B', hrows, hcols⟩ := lift_rowBasis B E C
  refine ⟨s, B', ?_⟩
  have hpivot : NormalFiber.pivot B' = NormalFiber.pivot C := by
    funext i j
    rw [NormalFiber.pivot, NormalFiber.pivot, hrows, hcols]
    exact congrFun (congrFun (append_reduced B E) (C.rows i)) (C.cols j)
  rw [hpivot]
  let dR : Fin r ⊕ extra → ℕ := Sum.elim (fun q => d (B.rows q)) (fun _ => 0)
  calc
    _ ≤ ∑ q, dR (C.rows q) := NormalFiber.minor_degree_le φ R s C dR
      (row_degree (M.submatrix B.rows id) E (fun q => d (B.rows q))
        (fun i j => hdeg (B.rows i) j))
    _ ≤ ∑ i, dR i := NormalFiber.selected_degree_sum_le C dR
    _ = _ := by simp [dR, Fintype.sum_sum_type]

end
end FrobeniusLocator.AppendConstants
end PackSource_AppendBudget

section PackSource_RowSelection
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K]
  [Fintype row] [Fintype col] [DecidableEq col]

/-- Extract a maximal row basis while retaining any prescribed linearly
independent group of rows. This is the cheap ordinary-row selection step. -/
theorem exists_rowBasis_containing (φ : F[X] →+* K) (M : Matrix row col F[X])
    (r : ℕ) (hr : (M.map φ).rank = r) (S : Set row)
    (hS : LinearIndepOn K (M.map φ).row S) :
    ∃ B : RowBasis φ M r, S ⊆ Set.range B.rows := by
  classical
  let N := M.map φ
  let T := hS.extend (Set.subset_univ S)
  have hST : S ⊆ T := hS.subset_extend (Set.subset_univ S)
  have hli : LinearIndependent K (fun i : T => N.row i.val) :=
    (hS.linearIndepOn_extend (Set.subset_univ S)).linearIndependent_restrict
  have hspace : Submodule.span K (Set.range (fun i : T => N.row i.val)) =
      Submodule.span K (Set.range N.row) := by
    have heq := hS.span_image_extend_eq_span_image (Set.subset_univ S)
    have hl : Set.range (fun i : T => N.row i.val) = N.row '' T := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [hl]
    simpa only [Set.image_univ] using heq
  have hcard : Fintype.card T = r := by
    rw [← finrank_span_eq_card hli, hspace, ← Matrix.rank_eq_finrank_span_row]
    exact hr
  let e : Fin r ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin r → row := fun q => (e q).val
  have hli' : LinearIndependent K (fun q : Fin r => N.row (rows q)) :=
    hli.comp e e.injective
  let A := N.submatrix rows id
  obtain ⟨cols, hcols⟩ := GenericRank.exists_rows_det_ne_zero A.transpose (by
    intro v hv
    have hsum : (∑ q, v q • N.row (rows q)) = 0 := by
      funext j
      have h := congrFun hv j
      change (∑ q, N (rows q) j * v q) = 0 at h
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        Matrix.row, Pi.zero_apply] using h
    funext q
    exact Fintype.linearIndependent_iff.mp hli' v hsum q)
  have hminorK : (N.submatrix rows cols).det ≠ 0 := by
    have heq : A.transpose.submatrix cols id = (N.submatrix rows cols).transpose := by
      funext i j
      rfl
    rw [heq, Matrix.det_transpose] at hcols
    exact hcols
  have hminor : (M.submatrix rows cols).det ≠ 0 := by
    intro hzero
    apply hminorK
    have hmap := φ.map_det (M.submatrix rows cols)
    rw [RingHom.mapMatrix_apply, hzero, map_zero] at hmap
    exact hmap.symm
  have hspace' : Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) =
      Submodule.span K (Set.range N.row) := by
    rw [← hspace]
    congr 1
    ext v
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨e q, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨l, hl⟩ := e.surjective q
      exact ⟨l, by simp only [rows, hl]⟩
  refine ⟨⟨rows, cols, hminor, ?_⟩, ?_⟩
  · intro i
    have hm : N.row i ∈ Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) := by
      rw [hspace']
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    refine ⟨a, ?_⟩
    intro j
    have h := congrFun ha j
    simpa only [N, Matrix.row, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
  · intro i hi
    obtain ⟨q, hq⟩ := e.surjective ⟨i, hST hi⟩
    exact ⟨q, congrArg Subtype.val hq⟩

end
end FrobeniusLocator.NormalFiber
end PackSource_RowSelection

section PackSource_AppendRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.AppendConstants
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators

variable {K row col : Type*} [Field K] [Fintype col] [DecidableEq col]

def functional (a : col → K) : (col → K) →ₗ[K] K where
  toFun v := ∑ j, a j * v j
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm, mul_assoc]

def appendOne (M : Matrix row col K) (a : col → K) : Matrix (row ⊕ Unit) col K :=
  appendOver M (fun _ => a)

theorem appendOne_kernel (M : Matrix row col K) (a v : col → K) :
    (appendOne M a).mulVec v = 0 ↔ M.mulVec v = 0 ∧ functional a v = 0 := by
  rw [appendOne, appendOver_kernel]
  constructor
  · rintro ⟨hM, ha⟩
    exact ⟨hM, congrFun ha ()⟩
  · rintro ⟨hM, ha⟩
    exact ⟨hM, funext (fun _ => ha)⟩

def restriction (M : Matrix row col K) (a : col → K) :
    LinearMap.ker M.mulVecLin →ₗ[K] K :=
  (functional a).comp (LinearMap.ker M.mulVecLin).subtype

def restrictionKernelEquiv (M : Matrix row col K) (a : col → K) :
    LinearMap.ker (restriction M a) ≃ₗ[K]
      LinearMap.ker (appendOne M a).mulVecLin where
  toFun v := ⟨v.val.val, (appendOne_kernel M a _).mpr ⟨v.val.property, v.property⟩⟩
  invFun v := ⟨⟨v.val, ((appendOne_kernel M a _).mp v.property).1⟩,
    ((appendOne_kernel M a _).mp v.property).2⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- The one-step pruning rank drop is derived from a non-common
functional, rather than assumed as a normal-fiber hypothesis. -/
theorem nullity_drop_one (M : Matrix row col K) (a : col → K)
    (hactive : ∃ v : col → K, M.mulVec v = 0 ∧ functional a v ≠ 0) :
    Module.finrank K (LinearMap.ker (appendOne M a).mulVecLin) + 1 =
      Module.finrank K (LinearMap.ker M.mulVecLin) := by
  have hne : restriction M a ≠ 0 := by
    intro hzero
    obtain ⟨v, hv, ha⟩ := hactive
    apply ha
    exact LinearMap.congr_fun hzero ⟨v, hv⟩
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [(restrictionKernelEquiv M a).finrank_eq] at h
  exact h

theorem rank_increases_one (M : Matrix row col K) (a : col → K)
    (hactive : ∃ v : col → K, M.mulVec v = 0 ∧ functional a v ≠ 0) :
    (appendOne M a).rank = M.rank + 1 := by
  have hdrop := nullity_drop_one M a hactive
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hA := LinearMap.finrank_range_add_finrank_ker (appendOne M a).mulVecLin
  change M.rank + _ = _ at hM
  change (appendOne M a).rank + _ = _ at hA
  rw [Module.finrank_fintype_fun_eq_card] at hM hA
  omega

theorem common_kernel_unchanged (M : Matrix row col K) (a : col → K)
    (hcommon : ∀ v, M.mulVec v = 0 → functional a v = 0) :
    LinearMap.ker (appendOne M a).mulVecLin = LinearMap.ker M.mulVecLin := by
  ext v
  exact ⟨fun h => ((appendOne_kernel M a v).mp h).1,
    fun h => (appendOne_kernel M a v).mpr ⟨h, hcommon v h⟩⟩

theorem rank_unchanged_iff_common (M : Matrix row col K) (a : col → K) :
    (appendOne M a).rank = M.rank ↔
      ∀ v, M.mulVec v = 0 → functional a v = 0 := by
  constructor
  · intro hr
    by_contra h
    push Not at h
    have hi := rank_increases_one M a h
    omega
  · intro hc
    have hk := common_kernel_unchanged M a hc
    have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have hA := LinearMap.finrank_range_add_finrank_ker (appendOne M a).mulVecLin
    change M.rank + _ = _ at hM
    change (appendOne M a).rank + _ = _ at hA
    rw [hk] at hA
    omega

end
end FrobeniusLocator.AppendConstants
end PackSource_AppendRank

section PackSource_RowDegreeSelection
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K]
  [Fintype row] [DecidableEq row] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}

theorem selected_two_level_sum (B : RowBasis φ M r) (S : Finset row)
    (hS : (S : Set row) ⊆ Set.range B.rows) (p : ℕ) :
    (∑ q, if B.rows q ∈ S then 1 else p) = S.card + p * (r - S.card) := by
  classical
  have hc : (Finset.univ.filter (fun q => B.rows q ∈ S)).card = S.card := by
    apply Finset.card_bij (fun q _ => B.rows q)
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · intro i hi j hj hij
      exact rows_injective B hij
    · intro i hi
      obtain ⟨q, hq⟩ := hS hi
      exact ⟨q, by simp [hq, hi], hq⟩
  have hn : (Finset.univ.filter (fun q => B.rows q ∉ S)).card = r - S.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (fun q => B.rows q ∈ S)
    rw [hc, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one, hc, hn]
  simp [Nat.mul_comm]

/-- The sharp ordinary/conjugate row ledger: retain every independent
degree-one row and pay degree p only for the remaining rank. -/
theorem exists_rowBasis_two_level (φ : F[X] →+* K) (M : Matrix row col F[X])
    (r : ℕ) (hr : (M.map φ).rank = r) (S : Finset row)
    (hS : LinearIndepOn K (M.map φ).row (S : Set row)) (p : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ if i ∈ S then 1 else p) :
    ∃ B : RowBasis φ M r,
      (∑ q, if B.rows q ∈ S then 1 else p) = S.card + p * (r - S.card) ∧
      (pivot B).det.natDegree ≤ S.card + p * (r - S.card) := by
  obtain ⟨B, hcontains⟩ := exists_rowBasis_containing φ M r hr (S : Set row) hS
  have heq := selected_two_level_sum B S hcontains p
  refine ⟨B, heq, ?_⟩
  rw [← heq]
  exact minor_degree_le φ M r B (fun i => if i ∈ S then 1 else p) hdeg

end
end FrobeniusLocator.NormalFiber
end PackSource_RowDegreeSelection

section PackSource_StackedRowBasis
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]

def ordinaryRows (L : ℕ) : Fin L → Fin 2 × Fin L := fun i => (0, i)

def ordinarySet (L : ℕ) : Finset (Fin 2 × Fin L) :=
  Finset.univ.filter (fun i => i.1 = 0)

theorem ordinarySet_coe (L : ℕ) :
    (ordinarySet L : Set (Fin 2 × Fin L)) = Set.range (ordinaryRows L) := by
  ext i
  constructor
  · intro hi
    have h0 : i.1 = 0 := (Finset.mem_filter.mp hi).2
    exact ⟨i.2, by ext <;> simp [ordinaryRows, h0]⟩
  · rintro ⟨i, rfl⟩
    simp [ordinarySet, ordinaryRows]

theorem ordinarySet_card (L : ℕ) : (ordinarySet L).card = L := by
  classical
  have heq : (ordinarySet L).card = (Finset.univ : Finset (Fin L)).card := by
    apply Finset.card_bij (fun i _ => i.2)
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      have hi0 := (Finset.mem_filter.mp hi).2
      have hj0 := (Finset.mem_filter.mp hj).2
      exact Prod.ext (hi0.trans hj0.symm) hij
    · intro j hj
      exact ⟨(0,j), by simp [ordinarySet], rfl⟩
  simpa using heq

/-- A sharp pivot certificate containing every ordinary row. -/
theorem exists_stacked_basis (φ : F[X] →+* K) (L s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) col F[X]) (hr : (M.map φ).rank = s)
    (hfirst : LinearIndependent K (fun i => (M.map φ).row (ordinaryRows L i)))
    (hdeg : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p) :
    ∃ B : RowBasis φ M s,
      (∑ q, if (B.rows q).1 = 0 then 1 else p) = L + p * (s-L) ∧
      (pivot B).det.natDegree ≤ L + p * (s-L) := by
  classical
  have hinj : Function.Injective (ordinaryRows L) := by
    intro i j hij
    exact congrArg Prod.snd hij
  have hS : LinearIndepOn K (M.map φ).row (ordinarySet L : Set (Fin 2 × Fin L)) := by
    rw [ordinarySet_coe]
    exact (linearIndepOn_range_iff hinj _).mpr hfirst
  have hdeg' : ∀ i j, (M i j).natDegree ≤ if i ∈ ordinarySet L then 1 else p := by
    intro i j
    simpa only [ordinarySet, Finset.mem_filter, Finset.mem_univ, true_and] using hdeg i j
  obtain ⟨B, hledger, hminor⟩ := exists_rowBasis_two_level φ M s hr (ordinarySet L) hS p hdeg'
  rw [ordinarySet_card] at hledger hminor
  refine ⟨B, ?_, ?_⟩
  · simpa only [ordinarySet, Finset.mem_filter, Finset.mem_univ, true_and,
      ordinarySet_card] using hledger
  · exact hminor

/-- The optimized initial ledger survives all constant evaluation rows. -/
theorem exists_stacked_append_budget {extra : Type*} [Fintype extra]
    (φ : F[X] →+* K) (L s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) col F[X]) (hr : (M.map φ).rank = s)
    (hfirst : LinearIndependent K (fun i => (M.map φ).row (ordinaryRows L i)))
    (hdeg : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p)
    (E : Matrix extra col F) :
    ∃ (s' : ℕ) (B : RowBasis φ (AppendConstants.append M E) s'),
      (pivot B).det.natDegree ≤ L + p * (s-L) := by
  obtain ⟨B, hledger, hminor⟩ := exists_stacked_basis φ L s p M hr hfirst hdeg
  obtain ⟨s', B', hb⟩ := AppendConstants.exists_append_basis_budget B E
    (fun i => if i.1 = 0 then 1 else p) hdeg
  exact ⟨s', B', by simpa only [hledger] using hb⟩

theorem first_rows_independent_of_rank (φ : F[X] →+* K) (L : ℕ)
    (M : Matrix (Fin 2 × Fin L) col F[X])
    (hfirst : ((M.map φ).submatrix (ordinaryRows L) id).rank = L) :
    LinearIndependent K (fun i => (M.map φ).row (ordinaryRows L i)) := by
  have hli : LinearIndependent K ((M.map φ).submatrix (ordinaryRows L) id).row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, Fintype.card_fin, hfirst]
  exact hli

end
end FrobeniusLocator.NormalFiber
end PackSource_StackedRowBasis

section PackSource_CommonRoots
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.CommonRoots
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {K row ι : Type*} [Field K] [DecidableEq ι]

def ofVector (t : ℕ) (v : Fin (t+1) → K) : K[X] :=
  ∑ j, monomial j.val (v j)

theorem ofVector_coeff (t : ℕ) (v : Fin (t+1) → K) (j : Fin (t+1)) :
    (ofVector t v).coeff j.val = v j := by
  simp only [ofVector, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have h : b.val ≠ j.val := fun h => hbj (Fin.ext h)
    simp [h]
  · simp

theorem ofVector_ne_zero (t : ℕ) (v : Fin (t+1) → K) (hv : v ≠ 0) :
    ofVector t v ≠ 0 := by
  intro hz
  apply hv
  funext j
  have h := ofVector_coeff t v j
  simpa only [hz, coeff_zero, Pi.zero_apply] using h.symm

theorem ofVector_natDegree_le (t : ℕ) (v : Fin (t+1) → K) :
    (ofVector t v).natDegree ≤ t := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le (v j)).trans (by omega)

theorem ofVector_eval (t : ℕ) (v : Fin (t+1) → K) (x : K) :
    (ofVector t v).eval x = AppendConstants.functional (fun j => x^j.val) v := by
  simp only [ofVector, eval_finsetSum, eval_monomial, AppendConstants.functional,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- Every common node root of a nonzero coefficient kernel is a root
of one nonzero degree-at-most-t polynomial. No normal-fiber assumption. -/
theorem card_le (t : ℕ) (M : Matrix row (Fin (t+1)) K)
    (x : ι → K) (hx : Function.Injective x) (H : Finset ι)
    (hcommon : ∀ i ∈ H, ∀ v, M.mulVec v = 0 →
      AppendConstants.functional (fun j => x i ^ j.val) v = 0)
    (hpositive : ∃ v : Fin (t+1) → K, v ≠ 0 ∧ M.mulVec v = 0) :
    H.card ≤ t := by
  classical
  obtain ⟨v, hv, hMv⟩ := hpositive
  have hP := ofVector_ne_zero t v hv
  have hcard : (H.image x).card ≤ (ofVector t v).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    apply (Polynomial.mem_roots hP).mpr
    change (ofVector t v).eval (x i) = 0
    rw [ofVector_eval]
    exact hcommon i hi v hMv
  rw [Finset.card_image_of_injective H hx] at hcard
  exact hcard.trans (ofVector_natDegree_le t v)

end
end FrobeniusLocator.CommonRoots
end PackSource_CommonRoots

section PackSource_PrincipalCount
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
local instance decidablePrincipal (P : Prop) : Decidable P := Classical.propDecidable P

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- One coefficient vector, polynomial in the slope parameter. -/
def specialize {d : ℕ} (v : Fin (d + 1) → F[X]) (γ : F) : F[X] :=
  ∑ j, C ((v j).eval γ) * X ^ j.val

/-- Evaluate the X-coordinate while retaining the slope variable. -/
def nodePolynomial {d : ℕ} (v : Fin (d + 1) → F[X]) (x : F) : F[X] :=
  ∑ j, C (x ^ j.val) * v j

theorem nodePolynomial_eval {d : ℕ} (v : Fin (d + 1) → F[X]) (x γ : F) :
    (nodePolynomial v x).eval γ = (specialize v γ).eval x := by
  simp only [nodePolynomial, specialize, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Each coefficient polynomial bounds every node evaluation polynomial. -/
theorem nodePolynomial_natDegree_le {d B : ℕ} (v : Fin (d + 1) → F[X])
    (hv : ∀ j, (v j).natDegree ≤ B) (x : F) :
    (nodePolynomial v x).natDegree ≤ B := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hv j)

theorem specialize_natDegree_le {d : ℕ} (v : Fin (d+1) → F[X]) (γ : F) :
    (specialize v γ).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have h := Polynomial.natDegree_C_mul_le ((v j).eval γ) (X ^ j.val : F[X])
  simp only [natDegree_X_pow] at h
  exact h.trans (by omega)

/-- Count roots in both directions. Every slope uses d distinct nodes;
each node has parameter degree at most p*d. No field-cardinality factor. -/
theorem principal_incidence_count (x : ι → F) (V : F → F[X])
    (q : ι → F[X]) (p d : ℕ) (hd : 0 < d)
    (hq : ∀ i, q i ≠ 0) (hdeg : ∀ i, (q i).natDegree ≤ p * d)
    (heval : ∀ i γ, (q i).eval γ = (V γ).eval (x i))
    (Γ : Finset F)
    (hroots : ∀ γ ∈ Γ, d ≤ (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card) :
    Γ.card ≤ p * Fintype.card ι := by
  classical
  have hnode (i : ι) :
      (Γ.filter (fun γ => (V γ).eval (x i) = 0)).card ≤ p * d := by
    apply le_trans (b := (q i).natDegree)
    · apply Polynomial.card_le_degree_of_subset_roots
      intro γ hγ
      apply (Polynomial.mem_roots (hq i)).mpr
      change (q i).eval γ = 0
      rw [heval]
      exact (Finset.mem_filter.mp hγ).2
    · exact hdeg i
  have hswap : (∑ γ ∈ Γ, (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card) =
      ∑ i : ι, (Γ.filter (fun γ => (V γ).eval (x i) = 0)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hleft : Γ.card * d ≤ ∑ γ ∈ Γ, (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card := by
    calc
      Γ.card * d = ∑ _γ ∈ Γ, d := by simp
      _ ≤ _ := Finset.sum_le_sum hroots
  have hright : (∑ i : ι, (Γ.filter
      (fun γ => (V γ).eval (x i) = 0)).card) ≤ Fintype.card ι * (p * d) := by
    calc
      _ ≤ ∑ _i : ι, p * d := Finset.sum_le_sum (fun i _ => hnode i)
      _ = _ := by simp
  rw [hswap] at hleft
  nlinarith

/-- Rank-drop exceptions are added once to the normal principal count. -/
theorem principal_kernel_count (x : ι → F) (V : F → F[X])
    (q : ι → F[X]) (p d δ : ℕ) (hd : 0 < d)
    (hq : ∀ i, q i ≠ 0) (hdeg : ∀ i, (q i).natDegree ≤ p * d)
    (heval : ∀ i γ, (q i).eval γ = (V γ).eval (x i))
    (Δ : F[X]) (hΔ : Δ ≠ 0) (hΔdeg : Δ.natDegree ≤ δ)
    (Γ : Finset F)
    (hroots : ∀ γ ∈ Γ, Δ.eval γ ≠ 0 → d ≤ (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card) :
    Γ.card ≤ δ + p * Fintype.card ι := by
  classical
  let E := Γ.filter (fun γ => Δ.eval γ = 0)
  let R := Γ.filter (fun γ => Δ.eval γ ≠ 0)
  have hE : E.card ≤ δ := by
    apply le_trans (b := Δ.natDegree)
    · apply Polynomial.card_le_degree_of_subset_roots
      intro γ hγ
      exact (Polynomial.mem_roots hΔ).mpr (Finset.mem_filter.mp hγ).2
    · exact hΔdeg
  have hR : R.card ≤ p * Fintype.card ι := by
    apply principal_incidence_count x V q p d hd hq hdeg heval R
    intro γ hγ
    obtain ⟨hγΓ, hγΔ⟩ := Finset.mem_filter.mp hγ
    exact hroots γ hγΓ hγΔ
  have hsum : E.card + R.card = Γ.card := by
    exact Finset.card_filter_add_card_filter_not _
  omega

end
end FrobeniusLocator.Principal
end PackSource_PrincipalCount

section PackSource_PrimitiveVector
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.PrimitiveVector
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators

variable {F col : Type*} [Field F] [Fintype col]

/-- Polynomial coordinates with no common nonunit factor. -/
def IsPrimitive (P : col → F[X]) : Prop := Ideal.span (Set.range P) = ⊤

theorem primitive_iff_bezout (P : col → F[X]) :
    IsPrimitive P ↔ ∃ a : col → F[X], ∑ i, a i * P i = 1 := by
  rw [IsPrimitive, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]

/-- Every nonzero polynomial vector has a primitive representative,
with its removed common factor recorded explicitly. -/
theorem exists_normalization (P : col → F[X]) (hP : P ≠ 0) :
    ∃ (g : F[X]) (Q : col → F[X]), g ≠ 0 ∧
      (∀ i, P i = g * Q i) ∧ IsPrimitive Q := by
  classical
  let I := Ideal.span (Set.range P)
  let g := Submodule.IsPrincipal.generator I
  have hg : g ≠ 0 := by
    intro hg
    have hI : I = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hg
    apply hP
    funext i
    have hm : P i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    rw [hI] at hm
    exact hm
  have hdiv : ∀ i, ∃ q : F[X], P i = g * q := by
    intro i
    have hm : P i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hm
    exact ⟨q, by simpa only [smul_eq_mul, mul_comm] using hq⟩
  choose Q hQ using hdiv
  refine ⟨g, Q, hg, hQ, (primitive_iff_bezout Q).mpr ?_⟩
  have hgm : g ∈ I := Submodule.IsPrincipal.generator_mem I
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgm
  refine ⟨a, ?_⟩
  have heq : g * (∑ i, a i * Q i) = g * 1 := by
    rw [Finset.mul_sum, mul_one]
    calc
      _ = ∑ i, a i * P i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hQ i]
        ring
      _ = g := ha
  exact mul_left_cancel₀ hg heq

theorem eval_ne_zero (P : col → F[X]) (hP : IsPrimitive P) (γ : F) :
    (fun i => (P i).eval γ) ≠ 0 := by
  obtain ⟨a, ha⟩ := (primitive_iff_bezout P).mp hP
  intro hzero
  have heval := congrArg (evalRingHom γ) ha
  simp only [map_sum, map_mul, map_one, Polynomial.coe_evalRingHom] at heval
  have hz : ∀ i, (P i).eval γ = 0 := fun i => congrFun hzero i
  simp only [hz, mul_zero, Finset.sum_const_zero] at heval
  exact zero_ne_one heval

theorem exists_eval_ne_zero (P : col → F[X]) (hP : IsPrimitive P) (γ : F) :
    ∃ i, (P i).eval γ ≠ 0 := by
  by_contra h
  push_neg at h
  exact eval_ne_zero P hP γ (funext h)

theorem normalization_natDegree_le (P Q : col → F[X]) (g : F[X]) (hg : g ≠ 0)
    (hPQ : ∀ i, P i = g * Q i) (i : col) :
    (Q i).natDegree ≤ (P i).natDegree := by
  by_cases hQ : Q i = 0
  · simp [hQ]
  · rw [hPQ i, Polynomial.natDegree_mul hg hQ]
    omega

theorem normalization_preserves_kernel {row : Type*} [DecidableEq col]
    (M : Matrix row col F[X]) (P Q : col → F[X]) (g : F[X]) (hg : g ≠ 0)
    (hPQ : ∀ i, P i = g * Q i) (hM : M.mulVec P = 0) :
    M.mulVec Q = 0 := by
  have heq : P = g • Q := by
    funext i
    exact hPQ i
  rw [heq, Matrix.mulVec_smul] at hM
  funext i
  have hi := congrFun hM i
  change g * (M.mulVec Q) i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left hg

end
end FrobeniusLocator.PrimitiveVector
end PackSource_PrimitiveVector

section PackSource_FreeCofactor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericCofactor
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}

theorem vector_pivot_zero (B : NormalFiber.RowBasis φ M r) (q : Fin r) :
    vector B (B.cols q) = 0 := by
  rw [vector, rawVector_apply]
  have hc : (M.submatrix B.rows B.cols).cramer (fun i => M (B.rows i) (B.cols q)) =
      Pi.single q (M.submatrix B.rows B.cols).det :=
    Matrix.cramer_row_self _ _ q (fun _ => rfl)
  rw [hc]
  funext c
  simp [Matrix.mulVec, dotProduct, inclusion, Pi.single_apply, mul_comm]

theorem vector_free_coordinate (B : NormalFiber.RowBasis φ M r) (j c : col)
    (hc : c ∉ Set.range B.cols) :
    vector B j c = if j = c then (NormalFiber.pivot B).det else 0 := by
  rw [vector, rawVector_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hzero : ∀ q, inclusion B.cols c q = (0 : F[X]) := by
    intro q
    have hq : B.cols q ≠ c := fun h => hc ⟨q, h⟩
    simp [inclusion, hq]
  simp only [hzero, zero_mul, Finset.sum_const_zero, sub_zero]
  by_cases hj : j = c <;> simp [hj, NormalFiber.pivot]

theorem normal_kernel_eq_free_span (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (γ : F)
    (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0) :
    LinearMap.ker (M.map (evalRingHom γ)).mulVecLin =
      Submodule.span F (Set.range (fun j : {j // j ∉ Set.range B.cols} =>
        fun c => (vector B j.val c).eval γ)) := by
  rw [normal_kernel_eq_span B hφ γ hγ]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j ∈ Set.range B.cols
    · obtain ⟨q, rfl⟩ := hj
      simp only [vector_pivot_zero, Pi.zero_apply, eval_zero]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      exact ⟨⟨j, hj⟩, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩

theorem free_evaluations_linearIndependent (B : NormalFiber.RowBasis φ M r)
    (γ : F) (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0) :
    LinearIndependent F (fun j : {j // j ∉ Set.range B.cols} =>
      fun c => (vector B j.val c).eval γ) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have h := congrFun ha j.val
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have hs : (∑ k : {j // j ∉ Set.range B.cols},
      a k * (vector B k.val j.val).eval γ) =
      a j * (NormalFiber.pivot B).det.eval γ := by
    rw [Finset.sum_eq_single j]
    · rw [vector_free_coordinate B j.val j.val j.property]
      simp
    · intro k hk hkj
      have hne : k.val ≠ j.val := fun hh => hkj (Subtype.ext hh)
      rw [vector_free_coordinate B k.val j.val j.property, if_neg hne, eval_zero, mul_zero]
    · simp
  rw [hs] at h
  exact (mul_eq_zero.mp h).resolve_right hγ

end
end FrobeniusLocator.GenericCofactor
end PackSource_FreeCofactor

section PackSource_GenericLayer
set_option autoImplicit true
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericLayer
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F row col : Type*} [Field F] [Fintype row] [Fintype col] [DecidableEq col]

abbrev GenericField (F : Type*) [Field F] := FractionRing F[X]

def genericRank (M : Matrix row col F[X]) : ℕ :=
  (M.map (algebraMap F[X] (GenericField F))).rank

def genericNullity (M : Matrix row col F[X]) : ℕ :=
  Module.finrank (GenericField F)
    (LinearMap.ker (M.map (algebraMap F[X] (GenericField F))).mulVecLin)

theorem rank_add_nullity (M : Matrix row col F[X]) :
    genericRank M + genericNullity M = Fintype.card col := by
  simpa only [genericRank, genericNullity, Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_range_add_finrank_ker
      (M.map (algebraMap F[X] (GenericField F))).mulVecLin

theorem exists_generic_basis (M : Matrix row col F[X]) :
    Nonempty (NormalFiber.RowBasis (algebraMap F[X] (GenericField F)) M (genericRank M)) :=
  NormalFiber.exists_rowBasis _ M _ rfl

/-- Generic common polynomial constraints pass to every normal fiber. -/
theorem common_constraint_normal (M : Matrix row col F[X])
    (B : NormalFiber.RowBasis (algebraMap F[X] (GenericField F)) M (genericRank M))
    (a : col → F[X])
    (ha : ∀ v : col → GenericField F,
      (M.map (algebraMap F[X] (GenericField F))).mulVec v = 0 →
      ∑ c, algebraMap F[X] (GenericField F) (a c) * v c = 0)
    (γ : F) (hγ : (NormalFiber.pivot B).det.eval γ ≠ 0)
    (v : col → F) (hv : (M.map (evalRingHom γ)).mulVec v = 0) :
    ∑ c, (a c).eval γ * v c = 0 :=
  GenericCofactor.common_functional_specializes B
    (IsFractionRing.injective F[X] (GenericField F)) a ha γ hγ v hv

/-- Zero generic nullity charges every nonzero specialized-kernel
event to the selected minor, with no further field-size dependence. -/
theorem zero_nullity_count (M : Matrix row col F[X]) (hnull : genericNullity M = 0)
    (B : NormalFiber.RowBasis (algebraMap F[X] (GenericField F)) M (genericRank M))
    (δ : ℕ) (hdeg : (NormalFiber.pivot B).det.natDegree ≤ δ)
    (Γ : Finset F)
    (hΓ : ∀ γ ∈ Γ, ∃ v : col → F, v ≠ 0 ∧
      (M.map (evalRingHom γ)).mulVec v = 0) : Γ.card ≤ δ := by
  have hr : genericRank M = Fintype.card col := by
    have h := rank_add_nullity M
    omega
  apply (Polynomial.card_le_degree_of_subset_roots ?_).trans hdeg
  intro γ hγ
  apply (Polynomial.mem_roots B.minor_ne).mpr
  by_contra hnormal
  have hR := NormalFiber.rank_specializes _
    (IsFractionRing.injective F[X] (GenericField F)) M _ B γ hnormal
  rw [hr] at hR
  obtain ⟨v, hv, hMv⟩ := hΓ γ hγ
  have hpositive : 0 < Module.finrank F
      (LinearMap.ker (M.map (evalRingHom γ)).mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨v, hMv⟩, ?_⟩
    intro hzero
    exact hv (congrArg Subtype.val hzero)
  have hdim := LinearMap.finrank_range_add_finrank_ker (M.map (evalRingHom γ)).mulVecLin
  change (M.map (evalRingHom γ)).rank + _ = _ at hdim
  rw [hR, Module.finrank_fintype_fun_eq_card] at hdim
  omega

theorem generic_common_roots_card {ι : Type*} [DecidableEq ι]
    (t : ℕ) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) (hx : Function.Injective x) (H : Finset ι)
    (hpositive : 0 < genericNullity M)
    (hcommon : ∀ i ∈ H, ∀ v : Fin (t+1) → GenericField F,
      (M.map (algebraMap F[X] (GenericField F))).mulVec v = 0 →
      ∑ j, algebraMap F[X] (GenericField F) (C (x i ^ j.val)) * v j = 0) :
    H.card ≤ t := by
  let φ := algebraMap F[X] (GenericField F)
  have hφ := IsFractionRing.injective F[X] (GenericField F)
  have hx' : Function.Injective (fun i => φ (C (x i))) :=
    hφ.comp (Polynomial.C_injective.comp hx)
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpositive
  have hne : v.val ≠ 0 := by
    intro hzero
    exact hv (Subtype.ext hzero)
  apply CommonRoots.card_le t (M.map φ) (fun i => φ (C (x i))) hx' H
  · intro i hi w hw
    have hh := hcommon i hi w hw
    simpa only [AppendConstants.functional, LinearMap.coe_mk,
      AddHom.coe_mk, map_pow] using hh
  · exact ⟨v.val, hne, v.property⟩

end
end FrobeniusLocator.GenericLayer
end PackSource_GenericLayer

section PackSource_PrincipalDivisor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
local instance decidableDivisor (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

theorem locator_eval_zero_iff (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (i : ι) : (locator x S).eval (x i) = 0 ↔ i ∈ S := by
  simp only [locator, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, sub_eq_zero, hx.eq_iff]
  simp

theorem locator_mul_sdiff (x : ι → F) (H S : Finset ι) (hHS : H ⊆ S) :
    locator x H * locator x (S \ H) = locator x S := by
  simpa only [locator, mul_comm] using
    (Finset.prod_sdiff (f := fun i => (X-C (x i) : F[X])) hHS)

/-- Removing the fixed squarefree domain factor leaves all remaining
generator roots outside the fixed nodes, with no incidence loss. -/
theorem remove_fixed_factor (x : ι → F) (hx : Function.Injective x)
    (H S : Finset ι) (V Q : F[X])
    (hfactor : locator x S = locator x H * V * Q) :
    V ∣ locator x (S \ H) ∧ ∀ i, V.eval (x i) = 0 → i ∉ H := by
  have hHS : H ⊆ S := by
    intro i hi
    apply (locator_eval_zero_iff x hx S i).mp
    rw [hfactor, eval_mul, eval_mul, locator_eval_zero x H i hi, zero_mul, zero_mul]
  have hcancel : locator x (S \ H) = V*Q := by
    apply mul_left_cancel₀ (locator_monic x H).ne_zero
    rw [locator_mul_sdiff x H S hHS, hfactor]
    ring
  refine ⟨⟨Q,hcancel⟩,?_⟩
  intro i hi
  have hz : (locator x (S \ H)).eval (x i) = 0 := by
    rw [hcancel, eval_mul, hi, zero_mul]
  exact (Finset.mem_sdiff.mp ((locator_eval_zero_iff x hx _ i).mp hz)).2

theorem roots_outside_fixed_card (x : ι → F) (H : Finset ι) (V : F[X])
    (havoid : ∀ i, V.eval (x i) = 0 → i ∉ H) :
    (Finset.univ.filter (fun i : {i // i ∉ H} => V.eval (x i.val) = 0)).card =
      (Finset.univ.filter (fun i => V.eval (x i) = 0)).card := by
  classical
  let D := Finset.univ.filter (fun i : {i // i ∉ H} => V.eval (x i.val) = 0)
  have himage : D.image Subtype.val =
      Finset.univ.filter (fun i => V.eval (x i) = 0) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      exact ⟨⟨i,havoid i hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]

theorem locator_roots (x : ι → F) (S : Finset ι) :
    (locator x S).roots = S.val.map x := by
  rw [locator, Polynomial.roots_prod _ _ (locator_monic x S).ne_zero]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

theorem locator_splits (x : ι → F) (S : Finset ι) : (locator x S).Splits := by
  exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C (x i))

/-- A divisor of a distinct-node locator has its full degree in distinct
domain roots. This is the X-side ingredient of the incidence count. -/
theorem divisor_domain_roots (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (V : F[X]) (hV : V ∣ locator x S) :
    V.natDegree = (Finset.univ.filter (fun i => V.eval (x i) = 0)).card := by
  classical
  have hE0 := (locator_monic x S).ne_zero
  have hV0 : V ≠ 0 := ne_zero_of_dvd_ne_zero hE0 hV
  have hsplits := (locator_splits x S).of_dvd hE0 hV
  have hle := Polynomial.roots.le_of_dvd hE0 hV
  rw [locator_roots] at hle
  have hnodup : V.roots.Nodup := Multiset.nodup_of_le hle (S.nodup.map hx)
  have himage : (Finset.univ.filter (fun i => V.eval (x i) = 0)).image x =
      V.roots.toFinset := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Polynomial.mem_roots hV0).mpr hi
    · intro ha
      have hEa := Multiset.mem_of_le hle ha
      obtain ⟨i, hiS, hia⟩ := Multiset.mem_map.mp hEa
      refine ⟨i, ?_, hia⟩
      change V.eval (x i) = 0
      rw [hia]
      exact (Polynomial.mem_roots hV0).mp ha
  calc
    V.natDegree = V.roots.card := hsplits.natDegree_eq_card_roots
    _ = V.roots.toFinset.card := (Multiset.toFinset_card_of_nodup hnodup).symm
    _ = ((Finset.univ.filter (fun i => V.eval (x i) = 0)).image x).card :=
      congrArg Finset.card himage.symm
    _ = _ := Finset.card_image_of_injective _ hx

/-- Full homogeneous degree is preserved whenever the split locator has
the prescribed total degree and the multiplier has its expected bound. -/
theorem full_degree_of_factorization (H V Q : F[X]) (h d q : ℕ)
    (hH : H.natDegree = h) (hV : V.natDegree ≤ d) (hQ : Q.natDegree ≤ q)
    (htotal : (H * V * Q).natDegree = h + d + q) : V.natDegree = d := by
  have htotal_le : (H * V * Q).natDegree ≤ h + V.natDegree + q := by
    calc
      _ ≤ (H * V).natDegree + Q.natDegree := Polynomial.natDegree_mul_le
      _ ≤ H.natDegree + V.natDegree + Q.natDegree :=
        Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ _ := by omega
  omega

end
end FrobeniusLocator.Principal
end PackSource_PrincipalDivisor

section PackSource_FrobeniusRankLayer
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericLayer
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- The ordinary block is literally the first family of stacked rows. -/
theorem stacked_ordinary (p : ℕ) [ExpChar F p] (x u v : ι → F) (L t : ℕ) :
    (stacked p x u v L t).submatrix (NormalFiber.ordinaryRows L) id =
      hankel x u v L t := by
  funext i j
  simp [stacked, NormalFiber.ordinaryRows]

/-- The polynomial-matrix certificate consumed by low-nullity pruning.
The two rank assumptions are explicit; no production input is classified. -/
theorem exists_frobenius_basis (p : ℕ) [ExpChar F p] (x u v : ι → F)
    (L t r : ℕ)
    (hr : genericRank (stacked p x u v L t) = t+1-r)
    (hfirst : genericRank (hankel x u v L t) = L) :
    ∃ B : NormalFiber.RowBasis (algebraMap F[X] (GenericField F))
        (stacked p x u v L t) (t+1-r),
      (∑ q, if (B.rows q).1 = 0 then 1 else p) = L + p * (t+1-r-L) ∧
      (NormalFiber.pivot B).det.natDegree ≤ L + p * (t+1-r-L) := by
  let φ := algebraMap F[X] (GenericField F)
  have hfirst' : (((stacked p x u v L t).map φ).submatrix
      (NormalFiber.ordinaryRows L) id).rank = L := by
    have heq : ((stacked p x u v L t).map φ).submatrix
        (NormalFiber.ordinaryRows L) id = (hankel x u v L t).map φ := by
      funext i j
      exact congrArg φ (congrFun (congrFun (stacked_ordinary p x u v L t) i) j)
    rw [heq]
    exact hfirst
  exact NormalFiber.exists_stacked_basis φ L (t+1-r) p _ hr
    (NormalFiber.first_rows_independent_of_rank φ L _ hfirst')
    (stacked_entry_natDegree p x u v L t)

theorem exists_frobenius_append_budget {extra : Type*} [Fintype extra]
    (p : ℕ) [ExpChar F p] (x u v : ι → F) (L t r : ℕ)
    (hr : genericRank (stacked p x u v L t) = t+1-r)
    (hfirst : genericRank (hankel x u v L t) = L)
    (E : Matrix extra (Fin (t+1)) F) :
    ∃ (s : ℕ) (B : NormalFiber.RowBasis (algebraMap F[X] (GenericField F))
        (AppendConstants.append (stacked p x u v L t) E) s),
      (NormalFiber.pivot B).det.natDegree ≤ L + p * (t+1-r-L) := by
  obtain ⟨B, hledger, hminor⟩ := exists_frobenius_basis p x u v L t r hr hfirst
  obtain ⟨s, B', hb⟩ := AppendConstants.exists_append_basis_budget B E
    (fun i => if i.1 = 0 then 1 else p) (stacked_entry_natDegree p x u v L t)
  exact ⟨s, B', by simpa only [hledger] using hb⟩

theorem exists_frobenius_basis_of_nullity (p : ℕ) [ExpChar F p] (x u v : ι → F)
    (L t r : ℕ) (hnull : genericNullity (stacked p x u v L t) = r)
    (hfirst : genericRank (hankel x u v L t) = L) :
    ∃ B : NormalFiber.RowBasis (algebraMap F[X] (GenericField F))
        (stacked p x u v L t) (t+1-r),
      (∑ q, if (B.rows q).1 = 0 then 1 else p) = L + p * (t+1-r-L) ∧
      (NormalFiber.pivot B).det.natDegree ≤ L + p * (t+1-r-L) := by
  have hr : genericRank (stacked p x u v L t) = t+1-r := by
    have h := rank_add_nullity (stacked p x u v L t)
    rw [hnull, Fintype.card_fin] at h
    omega
  exact exists_frobenius_basis p x u v L t r hr hfirst

end
end FrobeniusLocator.GenericLayer
end PackSource_FrobeniusRankLayer

section PackSource_PrimitiveLine
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericCofactor
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype row]
  [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}

/-- Normalize a cofactor while retaining its distinguished free
coordinate at every normal fiber. This also controls the leading-
coefficient/infinity issue when j is the top coefficient. -/
theorem normalize_free_cofactor (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (j : col) (hj : j ∉ Set.range B.cols)
    (d : row → ℕ) (hdeg : ∀ i c, (M i c).natDegree ≤ d i) :
    ∃ (g : F[X]) (Q : col → F[X]), g ≠ 0 ∧
      (∀ c, vector B j c = g * Q c) ∧ PrimitiveVector.IsPrimitive Q ∧
      M.mulVec Q = 0 ∧ (∀ c, (Q c).natDegree ≤ ∑ q, d (B.rows q)) ∧
      ∀ γ : F, (NormalFiber.pivot B).det.eval γ ≠ 0 →
        g.eval γ ≠ 0 ∧ (Q j).eval γ ≠ 0 := by
  have hP : vector B j ≠ 0 := by
    intro hzero
    have h := vector_free_coordinate B j j hj
    rw [if_pos rfl] at h
    apply B.minor_ne
    simpa only [NormalFiber.pivot, Pi.zero_apply] using
      h.symm.trans (congrFun hzero j)
  obtain ⟨g, Q, hg, hPQ, hprim⟩ := PrimitiveVector.exists_normalization (vector B j) hP
  have hQ := PrimitiveVector.normalization_preserves_kernel
    M (vector B j) Q g hg hPQ (annihilates B hφ j)
  refine ⟨g, Q, hg, hPQ, hprim, hQ, ?_, ?_⟩
  · intro c
    exact (PrimitiveVector.normalization_natDegree_le _ _ _ hg hPQ c).trans
      (vector_natDegree_le B d hdeg j c)
  · intro γ hγ
    have hprod : (NormalFiber.pivot B).det = g * Q j := by
      have h := vector_free_coordinate B j j hj
      rw [if_pos rfl] at h
      exact h.symm.trans (hPQ j)
    have heval : (NormalFiber.pivot B).det.eval γ = g.eval γ * (Q j).eval γ := by
      rw [hprod, eval_mul]
    rw [heval, mul_ne_zero_iff] at hγ
    exact hγ

/-- A one-dimensional generic kernel admits a primitive bounded-height
representative, and it spans every normal specialized kernel. -/
theorem exists_primitive_line (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (hnull : r + 1 = Fintype.card col)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) :
    ∃ Q : col → F[X], PrimitiveVector.IsPrimitive Q ∧ M.mulVec Q = 0 ∧
      (∀ c, (Q c).natDegree ≤ ∑ q, d (B.rows q)) ∧
      ∀ (γ : F), (NormalFiber.pivot B).det.eval γ ≠ 0 →
        ∀ v : col → F, (M.map (evalRingHom γ)).mulVec v = 0 →
          ∃ a : F, v = a • (fun c => (Q c).eval γ) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : col, j ∉ Set.range B.cols := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective B.cols := fun j => h j
    have hc := Fintype.card_le_of_surjective B.cols hsurj
    rw [Fintype.card_fin] at hc
    omega
  have hP : vector B j ≠ 0 := by
    intro hzero
    have h := vector_free_coordinate B j j hj
    rw [if_pos rfl] at h
    apply B.minor_ne
    simpa only [NormalFiber.pivot, Pi.zero_apply] using
      h.symm.trans (congrFun hzero j)
  obtain ⟨g, Q, hg, hPQ, hprim⟩ := PrimitiveVector.exists_normalization (vector B j) hP
  have hQ : M.mulVec Q = 0 := PrimitiveVector.normalization_preserves_kernel
    M (vector B j) Q g hg hPQ (annihilates B hφ j)
  refine ⟨Q, hprim, hQ, ?_, ?_⟩
  · intro c
    exact (PrimitiveVector.normalization_natDegree_le _ _ _ hg hPQ c).trans
      (vector_natDegree_le B d hdeg j c)
  · intro γ hγ v hv
    have hR := NormalFiber.rank_specializes φ hφ M r B γ hγ
    have hdim : Module.finrank F
        (LinearMap.ker (M.map (evalRingHom γ)).mulVecLin) = 1 := by
      have hh := LinearMap.finrank_range_add_finrank_ker (M.map (evalRingHom γ)).mulVecLin
      change (M.map (evalRingHom γ)).rank + _ = _ at hh
      rw [hR, Module.finrank_fintype_fun_eq_card] at hh
      omega
    have hQγ : (M.map (evalRingHom γ)).mulVec (fun c => (Q c).eval γ) = 0 := by
      funext i
      have h := congrArg (evalRingHom γ) (congrFun hQ i)
      simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
        Matrix.map_apply, Polynomial.coe_evalRingHom, Pi.zero_apply] using h
    exact GenericRank.kernel_line_of_finrank _ hdim _
      (PrimitiveVector.eval_ne_zero Q hprim γ) hQγ v hv

end
end FrobeniusLocator.GenericCofactor
end PackSource_PrimitiveLine

section PackSource_ExactTrimming
set_option autoImplicit true
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def ExtendsOn (x : ι → F) (w : ι → F) (k : ℕ) (S : Finset ι) : Prop :=
  ∃ P : F[X], P.degree < k ∧ ∀ i ∈ S, P.eval (x i) = w i

/-- Retain k interpolation anchors and one contradictory node, then pad to A. -/
theorem trim_nonextendable (x : ι → F) (hx : Function.Injective x)
    (w : ι → F) (k A : ℕ) (hkA : k < A) (S : Finset ι)
    (hAS : A ≤ S.card) (hbad : ¬ ExtendsOn x w k S) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = A ∧ ¬ ExtendsOn x w k T := by
  classical
  obtain ⟨B, hBS, hBcard⟩ := Finset.exists_subset_card_eq (show k ≤ S.card by omega)
  have hBinj : Set.InjOn x (B : Set ι) := fun a _ b _ h => hx h
  let q := Lagrange.interpolate B x w
  have hqdeg : q.degree < (k : WithBot ℕ) := by
    simpa only [q, hBcard] using Lagrange.degree_interpolate_lt w hBinj
  have hqval : ∀ i ∈ B, q.eval (x i) = w i :=
    fun i hi => Lagrange.eval_interpolate_at_node w hBinj hi
  obtain ⟨a, haS, ha⟩ : ∃ a ∈ S, q.eval (x a) ≠ w a := by
    by_contra hh
    push Not at hh
    exact hbad ⟨q, hqdeg, hh⟩
  have haB : a ∉ B := fun hh => ha (hqval a hh)
  have hins : insert a B ⊆ S := Finset.insert_subset_iff.mpr ⟨haS, hBS⟩
  have hsmall : (insert a B).card ≤ A := by
    rw [Finset.card_insert_of_notMem haB, hBcard]
    omega
  obtain ⟨T, hBT, hTS, hTcard⟩ := Finset.exists_subsuperset_card_eq hins hsmall hAS
  refine ⟨T, hTS, hTcard, ?_⟩
  rintro ⟨P, hP, hPv⟩
  have hpq : P = q := Polynomial.eq_of_degrees_lt_of_eval_index_eq B hBinj
    (by simpa only [hBcard] using hP) (by simpa only [hBcard] using hqdeg)
    (fun i hi => (hPv i (hBT (Finset.mem_insert_of_mem hi))).trans (hqval i hi).symm)
  exact ha (hpq ▸ hPv a (hBT (Finset.mem_insert_self a B)))

/-- A joint failure is preserved by choosing the subset for one failing input row. -/
theorem trim_nonjoint (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k A : ℕ) (hkA : k < A) (S : Finset ι)
    (hAS : A ≤ S.card) (hbad : ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = A ∧
      ¬ (ExtendsOn x u k T ∧ ExtendsOn x v k T) := by
  classical
  by_cases hu : ExtendsOn x u k S
  · obtain ⟨T, hTS, hTcard, hTbad⟩ := trim_nonextendable x hx v k A hkA S hAS
      (fun hv => hbad ⟨hu, hv⟩)
    exact ⟨T, hTS, hTcard, fun h => hTbad h.2⟩
  · obtain ⟨T, hTS, hTcard, hTbad⟩ := trim_nonextendable x hx u k A hkA S hAS hu
    exact ⟨T, hTS, hTcard, fun h => hTbad h.1⟩

/-- The ordinary decoder restricts to the same exact-A, still non-joint witness. -/
theorem exact_A_bad_witness (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (γ : F) (k A : ℕ) (hkA : k < A) (S : Finset ι)
    (hAS : A ≤ S.card) (P : F[X]) (hP : P.degree < k)
    (hfold : ∀ i ∈ S, P.eval (x i) = u i + γ * v i)
    (hbad : ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = A ∧ P.degree < k ∧
      (∀ i ∈ T, P.eval (x i) = u i + γ * v i) ∧
      ¬ (ExtendsOn x u k T ∧ ExtendsOn x v k T) := by
  obtain ⟨T, hTS, hcard, hbadT⟩ := trim_nonjoint x hx u v k A hkA S hAS hbad
  exact ⟨T, hTS, hcard, hP, fun i hi => hfold i (hTS hi), hbadT⟩

end
end FrobeniusLocator
end PackSource_ExactTrimming

section PackSource_LocatorConverse
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Parity equations for a locator times a received word. -/
def LocatorMoments (x : ι → F) (w : ι → F) (E : F[X]) (L : ℕ) : Prop :=
  ∀ j < L, ∑ i, weight x i * (E.eval (x i) * w i) * x i ^ j = 0

/-- The full set of locator recurrence equations gives an actual extension
on the complement. The exact dimension equality is part of the contract. -/
theorem extendsOn_of_locator_moments (x : ι → F) (hx : Function.Injective x)
    (w : ι → F) (k L : ℕ) (S : Finset ι)
    (hsize : k + L + S.card = Fintype.card ι)
    (hmom : LocatorMoments x w (locator x S) L) :
    ExtendsOn x w k (Finset.univ \ S) := by
  classical
  let T := Finset.univ \ S
  let P := Lagrange.interpolate T x w
  have hTcard : T.card = Fintype.card ι - S.card := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  have hPinj : Set.InjOn x (T : Set ι) := hx.injOn
  have hPval : ∀ i ∈ T, P.eval (x i) = w i :=
    fun i hi => Lagrange.eval_interpolate_at_node w hPinj hi
  refine ⟨P, ?_, hPval⟩
  by_contra hP
  have hp0 : P ≠ 0 := by
    intro hz
    simp [hz] at hP
  have hPnat : k ≤ P.natDegree := by
    have hnot := not_lt.mp hP
    exact_mod_cast hnot.trans Polynomial.degree_le_natDegree
  have hPbound : P.natDegree < Fintype.card ι - S.card := by
    apply (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr
    simpa only [P, hTcard] using Lagrange.degree_interpolate_lt w hPinj
  let j := Fintype.card ι - 1 - S.card - P.natDegree
  have hj : j < L := by omega
  have htop : S.card + P.natDegree + j = Fintype.card ι - 1 := by omega
  let Q := locator x S * P * X ^ j
  have hE0 : locator x S ≠ 0 := (locator_monic x S).ne_zero
  have hQdeg : Q.natDegree = Fintype.card ι - 1 := by
    dsimp [Q]
    rw [natDegree_mul (mul_ne_zero hE0 hp0) (pow_ne_zero _ X_ne_zero),
      natDegree_mul hE0 hp0, locator_natDegree, natDegree_X_pow, htop]
  have hQlt : Q.degree < (Fintype.card ι : WithBot ℕ) := by
    apply Polynomial.degree_le_natDegree.trans_lt
    rw [hQdeg]
    exact_mod_cast (show Fintype.card ι - 1 < Fintype.card ι by omega)
  have hcoeff := Lagrange.coeff_eq_sum (s := Finset.univ) (v := x)
    (fun a _ b _ hab => hx hab) (by simpa using hQlt)
  have hpoint (i : ι) :
      (locator x S).eval (x i) * P.eval (x i) =
      (locator x S).eval (x i) * w i := by
    by_cases hi : i ∈ S
    · simp [locator_eval_zero x S i hi]
    · rw [hPval i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)]
  have hsum : ∑ i, weight x i * Q.eval (x i) = 0 := by
    dsimp [Q]
    simp only [eval_mul, eval_pow, eval_X]
    simp_rw [hpoint]
    simpa only [mul_assoc] using hmom j hj
  have hz : Q.coeff (Fintype.card ι - 1) = 0 := by
    have hc : Q.coeff (Fintype.card ι - 1) =
        ∑ i, weight x i * Q.eval (x i) := by
      simpa only [Finset.card_univ, weight, div_eq_mul_inv, mul_comm] using hcoeff
    exact hc.trans hsum
  have hQ0 : Q ≠ 0 := mul_ne_zero (mul_ne_zero hE0 hp0) (pow_ne_zero _ X_ne_zero)
  apply (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
  simpa only [Polynomial.leadingCoeff, hQdeg] using hz

/-- Ordinary Hankel recurrences and locator moments are the same sums. -/
theorem hankel_word_moments (x : ι → F) (w : ι → F) (E : F[X]) (L t : ℕ)
    (hE : E.natDegree ≤ t)
    (hrec : ∀ i : Fin L, ∑ j : Fin (t+1),
      syndrome x w (i.val+j.val) * E.coeff j.val = 0) :
    LocatorMoments x w E L := by
  intro i hi
  have hh := hrec ⟨i, hi⟩
  have hsum : (∑ j : Fin (t+1), syndrome x w (i+j.val) * E.coeff j.val) =
      ∑ a, weight x a * (E.eval (x a) * w a) * x a ^ i := by
    simp only [syndrome, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← sum_coeff_eval E t hE (x a)]
    simp only [Finset.sum_mul, Finset.mul_sum, pow_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact hsum.symm.trans hh

end
end FrobeniusLocator.Principal
end PackSource_LocatorConverse

section PackSource_TwistedTranspose
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {K : Type*} [Field K]

/-- A two-functional Hankel window with literal row and column counts. -/
def hankelWindow (s : Fin 2 → ℕ → K) (rows cols : ℕ) :
    Matrix (Fin 2 × Fin rows) (Fin cols) K :=
  fun b j => s b.1 (b.2.val+j.val)

/-- Degree-H twisted relation map: exactly the transposed complementary
Hankel window. The m-H columns of that window are degrees 0,...,m-H-1. -/
def relationMatrix (s : Fin 2 → ℕ → K) (m H : ℕ) :
    Matrix (Fin (m-H)) (Fin 2 × Fin (H+1)) K :=
  (hankelWindow s (H+1) (m-H)).transpose

theorem relationMatrix_entry (s : Fin 2 → ℕ → K) (m H : ℕ)
    (j : Fin (m-H)) (b : Fin 2 × Fin (H+1)) :
    relationMatrix s m H j b=s b.1 (b.2.val+j.val) := rfl

/-- The relation equations are the contraction equations, with both
functional blocks and the boundary indices explicit. -/
theorem relation_equations (s : Fin 2 → ℕ → K) (m H : ℕ)
    (v : Fin 2 × Fin (H+1) → K) :
    (relationMatrix s m H).mulVec v=0 ↔
      ∀ j : Fin (m-H), ∑ b : Fin 2, ∑ i : Fin (H+1),
        v (b,i)*s b (i.val+j.val)=0 := by
  simp only [funext_iff, Matrix.mulVec, dotProduct, relationMatrix, hankelWindow,
    Matrix.transpose_apply, Pi.zero_apply, Fintype.sum_prod_type, mul_comm]

/-- Transpose plus rank-nullity. This is independent of any apolar
resolution theorem and is valid over every field. -/
theorem complementary_nullities (s : Fin 2 → ℕ → K) (m H : ℕ) :
    Module.finrank K (LinearMap.ker (relationMatrix s m H).mulVecLin)+(m-H) =
      2*(H+1)+Module.finrank K
        (LinearMap.ker (hankelWindow s (H+1) (m-H)).mulVecLin) := by
  have hr := LinearMap.finrank_range_add_finrank_ker (relationMatrix s m H).mulVecLin
  have hk := LinearMap.finrank_range_add_finrank_ker
    (hankelWindow s (H+1) (m-H)).mulVecLin
  change (relationMatrix s m H).rank + _ = _ at hr
  change (hankelWindow s (H+1) (m-H)).rank + _ = _ at hk
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hr
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hk
  have he : (relationMatrix s m H).rank=(hankelWindow s (H+1) (m-H)).rank :=
    Matrix.rank_transpose _
  omega

/-- The exact Hilbert-function input still needed from the binary level
resolution. It is stated on actual Hankel kernels, not encoded as an axiom. -/
def HasLevelHilbertFunction (s : Fin 2 → ℕ → K) (m a b c : ℕ) : Prop :=
  ∀ H<m, Module.finrank K
    (LinearMap.ker (hankelWindow s (H+1) (m-H)).mulVecLin) =
      (m-H-a)+(m-H-b)+(m-H-c)

/-- On the two-active range, the relation space has exactly H-h+1
parameters. Existence of the Hilbert function is an explicit premise. -/
theorem relation_nullity_on_two_active (s : Fin 2 → ℕ → K)
    (m a b c H : ℕ) (hc : c≤m) (hsum : a+b+c=2*m+2)
    (ha : a≤b) (hb : b≤m-H) (hH : m+1-c≤H) (hHm : H<m)
    (hHF : HasLevelHilbertFunction s m a b c) :
    Module.finrank K (LinearMap.ker (relationMatrix s m H).mulVecLin) =
      H-(m+1-c)+1 := by
  have hd := complementary_nullities s m H
  rw [hHF H hHm] at hd
  omega

/-- The minimum-degree relation is a line in the genuine two-active
range (the largest generator occurs once). -/
theorem minimal_relation_line (s : Fin 2 → ℕ → K)
    (m a b c : ℕ) (hc : c≤m) (hsum : a+b+c=2*m+2)
    (ha : a≤b) (hb : b<c) (hc2 : 1<c)
    (hHF : HasLevelHilbertFunction s m a b c) :
    Module.finrank K (LinearMap.ker (relationMatrix s m (m+1-c)).mulVecLin)=1 := by
  have h := relation_nullity_on_two_active s m a b c (m+1-c) hc hsum ha
    (by omega) (by omega) (by omega) hHF
  simpa using h

end
end FrobeniusLocator.Strata
end PackSource_TwistedTranspose

section PackSource_SyndromeConverse
set_option autoImplicit true
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- Completeness of all ordinary RS parity checks, proved by interpolation. -/
theorem extendsOn_of_syndrome_zero (x : ι → F) (hx : Function.Injective x)
    (w : ι → F) (k : ℕ) (hk : k ≤ Fintype.card ι)
    (hzero : ∀ j < Fintype.card ι-k, syndrome x w j = 0) :
    ExtendsOn x w k Finset.univ := by
  have hmom : LocatorMoments x w (locator x ∅) (Fintype.card ι-k) := by
    intro j hj
    simpa [syndrome, locator] using hzero j hj
  simpa using extendsOn_of_locator_moments x hx w k (Fintype.card ι-k) ∅
    (by simp; omega) hmom

theorem syndrome_linear (x u v : ι → F) (a b : F) (j : ℕ) :
    syndrome x (fun i => a*u i+b*v i) j = a*syndrome x u j+b*syndrome x v j := by
  simp only [syndrome, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end
end FrobeniusLocator.Principal
end PackSource_SyndromeConverse

section PackSource_C42BlockMatrixRank
set_option autoImplicit true
/-! Generic finite block-dimension rank lemma. Applying it to C42 still
requires the actual coefficient support/translation identifications. -/
namespace Sol1.C42

open scoped BigOperators Matrix

open Classical in
theorem matrix_rank_le_sum_min_fibers
    {E Row Col Block : Type*} [Field E] [Fintype Row] [Fintype Col] [Fintype Block]
    (M : Matrix Row Col E) (rowBlock : Row → Block) (colBlock : Col → Block)
    (hzero : ∀ i j, rowBlock i ≠ colBlock j → M i j = 0) :
    M.rank ≤ ∑ b : Block, min
      (Finset.univ.filter fun i ↦ rowBlock i = b).card
      (Finset.univ.filter fun j ↦ colBlock j = b).card := by
  classical
  let part : Block → Matrix Row Col E := fun b i j ↦ if rowBlock i = b then M i j else 0
  let stacked : Matrix (Block × Row) Col E := fun bi j ↦ part bi.1 bi.2 j
  have hrecover : stacked.submatrix (fun i ↦ (rowBlock i, i)) id = M := by
    ext i j
    change (if rowBlock i = rowBlock i then M i j else 0) = M i j
    simp
  have hrow : ∀ b, (part b).rank ≤ (Finset.univ.filter fun i ↦ rowBlock i = b).card := by
    intro b
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro i hi
    have hne : rowBlock i ≠ b := by simpa using hi
    funext j
    change (if rowBlock i = b then M i j else 0) = 0
    simp [hne]
  have hcol : ∀ b, (part b).rank ≤ (Finset.univ.filter fun j ↦ colBlock j = b).card := by
    intro b
    rw [← Matrix.rank_transpose (part b)]
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro j hj
    have hne : colBlock j ≠ b := by simpa using hj
    funext i
    change (if rowBlock i = b then M i j else 0) = 0
    by_cases hi : rowBlock i = b
    · rw [ite_eq_left hi]
      apply hzero i j
      intro heq
      exact hne (heq.symm.trans hi)
    · simp [hi]
  calc
    M.rank = (stacked.submatrix (fun i ↦ (rowBlock i, i)) id).rank := by rw [hrecover]
    _ ≤ stacked.rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ ∑ b : Block, (part b).rank := Matrix.rank_prod_rows_le_sum stacked
    _ ≤ ∑ b : Block, min
        (Finset.univ.filter fun i ↦ rowBlock i = b).card
        (Finset.univ.filter fun j ↦ colBlock j = b).card :=
      Finset.sum_le_sum fun b _ ↦ le_min (hrow b) (hcol b)

open Classical in
theorem matrix_rank_le_sum_min_bounds
    {E Row Col Block : Type*} [Field E] [Fintype Row] [Fintype Col] [Fintype Block]
    (M : Matrix Row Col E) (rowBlock : Row → Block) (colBlock : Col → Block)
    (r c : Block → ℕ)
    (hzero : ∀ i j, rowBlock i ≠ colBlock j → M i j = 0)
    (hr : ∀ b, (Finset.univ.filter fun i ↦ rowBlock i = b).card ≤ r b)
    (hc : ∀ b, (Finset.univ.filter fun j ↦ colBlock j = b).card ≤ c b) :
    M.rank ≤ ∑ b, min (r b) (c b) := by
  exact (matrix_rank_le_sum_min_fibers M rowBlock colBlock hzero).trans
    (Finset.sum_le_sum fun b _ ↦ min_le_min (hr b) (hc b))


end Sol1.C42
end PackSource_C42BlockMatrixRank

section PackSource_C52MatrixReduction
set_option autoImplicit true
namespace Sol1.C52
open scoped BigOperators Matrix
noncomputable section

/-- Restriction to a finite family containing every nonzero column up to equality. -/
theorem rank_le_col_representatives
    {F R C C' : Type*} [Field F] [Fintype C] [Fintype C']
    (M : Matrix R C F) (rep : C' → C)
    (h : ∀ c, M.col c = 0 ∨ ∃ j, M.col c = M.col (rep j)) :
    M.rank ≤ (M.submatrix id rep).rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (M.submatrix id rep).col)
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  rcases h c with hz | ⟨j,hj⟩
  · rw [hz]
    exact Submodule.zero_mem _
  · rw [hj]
    exact Submodule.subset_span ⟨j,rfl⟩

/-- Restriction to finite row representatives, allowing the remaining rows to be zero. -/
theorem rank_le_row_representatives
    {F R C R' : Type*} [Field F] [Fintype C] [Fintype R']
    (M : Matrix R C F) (rep : R' → R)
    (h : ∀ r, M r = 0 ∨ ∃ j, M r = M (rep j)) :
    M.rank ≤ (M.submatrix rep id).rank := by
  classical
  let hasRep (r : R) : Prop := ∃ j, M r = M (rep j)
  let selector : Matrix R R' F := fun r j ↦
    if hr : hasRep r then if j = hr.choose then 1 else 0 else 0
  have hfactor : selector * M.submatrix rep id = M := by
    ext r c
    change (∑ j : R', selector r j * M (rep j) c) = M r c
    by_cases hr : hasRep r
    · simp only [selector, dite_eq_left hr]
      rw [Finset.sum_eq_single hr.choose]
      · simpa using congrFun hr.choose_spec c |>.symm
      · intro b _ hb
        simp [hb]
      · simp
    · have hz : M r = 0 := (h r).resolve_right hr
      simp [selector, hr, congrFun hz c]
  calc M.rank = (selector * M.submatrix rep id).rank := congrArg Matrix.rank hfactor.symm
    _ ≤ (M.submatrix rep id).rank := Matrix.rank_mul_le_right _ _

/-- A dependent row/column block matrix has rank bounded by the sum of the fiber minima. -/
theorem rank_le_sum_min_dependent
    {F B : Type*} [Field F] [Fintype B]
    {R C : B → Type*} [∀ b, Fintype (R b)] [∀ b, Fintype (C b)]
    (M : Matrix (Sigma R) (Sigma C) F)
    (hzero : ∀ i j, i.1 ≠ j.1 → M i j = 0) :
    M.rank ≤ ∑ b, min (Fintype.card (R b)) (Fintype.card (C b)) := by
  classical
  apply Sol1.C42.matrix_rank_le_sum_min_bounds M Sigma.fst Sigma.fst
    (fun b ↦ Fintype.card (R b)) (fun b ↦ Fintype.card (C b)) hzero
  · intro b
    have he : {i : Sigma R // i.1 = b} ≃ R b :=
      { toFun := fun i ↦ i.2 ▸ i.1.2
        invFun := fun r ↦ ⟨⟨b,r⟩,rfl⟩
        left_inv := by rintro ⟨⟨b',r⟩,h⟩; cases h; rfl
        right_inv := fun _ ↦ rfl }
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr he).le
  · intro b
    have he : {i : Sigma C // i.1 = b} ≃ C b :=
      { toFun := fun i ↦ i.2 ▸ i.1.2
        invFun := fun c ↦ ⟨⟨b,c⟩,rfl⟩
        left_inv := by rintro ⟨⟨b',c⟩,h⟩; cases h; rfl
        right_inv := fun _ ↦ rfl }
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr he).le

end
end Sol1.C52
end PackSource_C52MatrixReduction

section PackSource_C64Mobius
set_option autoImplicit true
namespace Sol1.C64
noncomputable section
variable {F K : Type*} [Field F] [Field K]

def tailRatio (u v a b gamma : K) : K := (u + gamma*v)/(a + gamma*b)

theorem tailRatio_injective (u v a b : K) (hminor : u*b-v*a ≠ 0)
    (gamma eta : K) (hgamma : a+gamma*b ≠ 0) (heta : a+eta*b ≠ 0)
    (heq : tailRatio u v a b gamma = tailRatio u v a b eta) : gamma = eta := by
  have hcross := (div_eq_div_iff hgamma heta).mp heq
  have hz : (gamma-eta)*(u*b-v*a) = 0 := by linear_combination -hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hminor)

/-- Actual finite sets whose injective Mobius coordinate lies in a base field cost at most |F|. -/
theorem tailRatio_card_le [Fintype F] (phi : F →+* K) (u v a b : K)
    (hminor : u*b-v*a ≠ 0) (S : Finset K)
    (hden : ∀ gamma ∈ S, a+gamma*b ≠ 0)
    (hbase : ∀ gamma ∈ S, ∃ c : F, phi c = tailRatio u v a b gamma) :
    S.card ≤ Fintype.card F := by
  classical
  choose c hc using fun gamma : S ↦ hbase gamma.val gamma.property
  have hinj : Function.Injective c := by
    intro gamma eta heq
    apply Subtype.ext
    apply tailRatio_injective u v a b hminor gamma eta
      (hden gamma.val gamma.property) (hden eta.val eta.property)
    rw [← hc gamma,← hc eta,heq]
  exact (Fintype.card_coe S).symm.trans_le (Fintype.card_le_of_injective c hinj)

end
end Sol1.C64
end PackSource_C64Mobius

section PackSource_C64LocatorCore
set_option autoImplicit true
namespace Sol1.C64
open Polynomial
noncomputable section
open scoped BigOperators
variable {F K I : Type*} [Field F] [Field K]

def baseLocator (nodes : I → F) (T : Finset I) : F[X] := ∏ i ∈ T, (X-C (nodes i))

/-- Saturating the degree bound by distinct base-field roots gives the exact locator. -/
theorem locator_shape (phi : F →+* K) (nodes : I ↪ F) (T : Finset I)
    (r : K[X]) (hr : r ≠ 0) (hdegree : r.natDegree ≤ T.card)
    (hroot : ∀ i ∈ T, r.eval (phi (nodes i)) = 0) :
    r = C (r.coeff T.card) * (baseLocator nodes T).map phi := by
  classical
  let lift : I → K := fun i ↦ phi (nodes i)
  have hinj : Function.Injective lift := phi.injective.comp nodes.injective
  let S := T.image lift
  have hScard : S.card = T.card := Finset.card_image_of_injective T hinj
  have hSroot : ∀ x ∈ S, r.eval x = 0 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact hroot i hi
  have hcard : T.card ≤ r.natDegree :=
    Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hr hinj.injOn hroot
  have hnad : r.natDegree = T.card := Nat.le_antisymm hdegree hcard
  have hroots : r.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero hSroot
    (by rw [hScard,hnad]) hr
  have hshape := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := r)
    (by rw [hroots]; change S.card = r.natDegree; rw [hScard,hnad])
  have hprod : (r.roots.map fun a ↦ X-C a).prod = (baseLocator nodes T).map phi := by
    rw [hroots]
    change (∏ x ∈ S, (X-C x)) = _
    rw [show S = T.image lift from rfl,Finset.prod_image]
    · simp [baseLocator,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,lift]
    · exact fun x _ y _ hxy ↦ hinj hxy
  rw [hprod,show r.leadingCoeff = r.coeff T.card by rw [← hnad]; rfl] at hshape
  exact hshape.symm

theorem locator_tail_ratio (phi : F →+* K) (nodes : I ↪ F) (T : Finset I)
    (r : K[X]) (hr : r ≠ 0) (hdegree : r.natDegree ≤ T.card)
    (hroot : ∀ i ∈ T, r.eval (phi (nodes i)) = 0) (j : ℕ) :
    ∃ c : F, phi c = r.coeff j / r.coeff T.card := by
  have hshape := locator_shape phi nodes T r hr hdegree hroot
  have hcard : T.card ≤ r.natDegree :=
    Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hr
      (phi.injective.comp nodes.injective).injOn hroot
  have hnad : r.natDegree = T.card := Nat.le_antisymm hdegree hcard
  have hlead : r.coeff T.card ≠ 0 := by
    rw [← hnad]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hr
  refine ⟨(baseLocator nodes T).coeff j, ?_⟩
  have hc := congrArg (fun p : K[X] ↦ p.coeff j) hshape
  simp only [coeff_C_mul,coeff_map] at hc
  rw [hc]
  field_simp

theorem root_saturation (phi : F →+* K) (nodes : I ↪ F) (T : Finset I)
    (r : K[X]) (hr : r ≠ 0) (A : ℕ) (hdegree : r.natDegree ≤ A) (hcard : A ≤ T.card)
    (hroot : ∀ i ∈ T, r.eval (phi (nodes i)) = 0) :
    r.natDegree = A ∧ T.card = A := by
  have hh := Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hr
    (phi.injective.comp nodes.injective).injOn hroot
  omega

end
end Sol1.C64
end PackSource_C64LocatorCore

section PackSource_K1_11CertificateArithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11
open Finset

/-- Exact number of source monomials. D is an inclusive weighted bound. -/
def V (D w B s t : ℕ) : ℕ :=
  ∑ i ∈ range (B+1), ∑ j ∈ range (B+1-i),
    (D+1-w*(i+j))*(s+1-i)*(t+1-j)

/-- Truncated three-contact-variable monomial count with parameter weights. -/
def J (m s t : ℕ) : ℕ :=
  ∑ i ∈ range m, ∑ j ∈ range (m-i),
    (m-i-j)*(s+1-i)*(t+1-j)

end K1_11
end PackSource_K1_11CertificateArithmetic

section PackSource_K1_11Elimination
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open Polynomial Finset

/-- Homogeneous denominator clearing. It remains meaningful at b=0. -/
def clearedEval {R : Type*} [CommRing R] (B : ℕ) (Q : R[X]) (a b : R) : R :=
  ∑ j∈range (B+1),Q.coeff j*a^j*b^(B-j)

/-- Denominator clearing commutes with every actual root specialization,
including b=0. This is the identity needed for the SAME original decoder. -/
theorem clearedEval_at_root {R : Type*} [CommRing R]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b y : R) (hy : b*y=a) :
    clearedEval B Q a b=b^B*Q.eval y := by
  rw [eval_eq_sum_range' (show Q.natDegree<B+1 by omega),mul_sum]
  unfold clearedEval
  apply sum_congr rfl
  intro j hj
  have hjB : j≤B := by have := mem_range.mp hj; omega
  rw [← hy,mul_pow]
  have hb : b^j*b^(B-j)=b^B := by rw [← pow_add,Nat.add_sub_of_le hjB]
  calc
    Q.coeff j*(b^j*y^j)*b^(B-j) = Q.coeff j*y^j*(b^j*b^(B-j)) := by ring
    _ = b^B*(Q.coeff j*y^j) := by rw [hb]; ring

theorem clearedEval_zero_of_root {R : Type*} [CommRing R]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b y : R)
    (hy : b*y=a) (hroot : Q.eval y=0) : clearedEval B Q a b=0 := by
  rw [clearedEval_at_root B Q hQ a b y hy,hroot,mul_zero]

/-- Over a field, a nonmultiple survives linear elimination. -/
theorem clearedEval_ne_zero_field {K : Type*} [Field K]
    (B : ℕ) (Q : K[X]) (hQ : Q.natDegree≤B) (a b : K) (hb : b≠0)
    (hnot : ¬ (C b*X-C a) ∣ Q) : clearedEval B Q a b≠0 := by
  have heq : C b*X-C a=C b*(X-C (a/b)) := by
    rw [mul_sub,← C_mul]
    have hba : b*(a/b)=a := by field_simp
    rw [hba]
  have hroot : Q.eval (a/b)≠0 := by
    intro hz
    apply hnot
    rw [heq]
    have hd : (X-C (a/b))∣Q := (dvd_iff_isRoot).mpr hz
    have hu : C b ∣ (1 : K[X]) := (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)).dvd
    simpa using mul_dvd_mul hu hd
  rw [clearedEval_at_root B Q hQ a b (a/b) (by field_simp)]
  exact mul_ne_zero (pow_ne_zero B hb) hroot

/-- The coefficient-ring map respects the cleared expression. -/
theorem map_clearedEval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (B : ℕ) (Q : R[X]) (a b : R) :
    f (clearedEval B Q a b)=clearedEval B (Q.map f) (f a) (f b) := by
  simp [clearedEval]

/-- Primitive linear elimination over any GCD domain. Gauss transfers
nondivisibility to the fraction field. -/
theorem clearedEval_ne_zero {R K : Type*} [CommRing R] [IsDomain R]
    [IsGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b : R) (hb : b≠0)
    (hprimitive : (C b*X-C a).IsPrimitive) (hnot : ¬ (C b*X-C a)∣Q) :
    clearedEval B Q a b≠0 := by
  have hmap : ¬ (C (algebraMap R K b)*X-C (algebraMap R K a))∣Q.map (algebraMap R K) := by
    simpa only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X] using
      (not_congr (hprimitive.dvd_iff_fraction_map_dvd_fraction_map K)).mp hnot
  have hdeg : (Q.map (algebraMap R K)).natDegree≤B := (natDegree_map_le).trans hQ
  have hb' : algebraMap R K b≠0 := by simpa using (IsFractionRing.injective R K).ne hb
  have hn := clearedEval_ne_zero_field B (Q.map (algebraMap R K)) hdeg
    (algebraMap R K a) (algebraMap R K b) hb' hmap
  rw [← map_clearedEval] at hn
  exact fun hz => hn (by rw [hz,map_zero])

end
end K1_11
end PackSource_K1_11Elimination

section PackSource_K1_2SharedIncidence
set_option autoImplicit true
set_option autoImplicit false

/-! One fixed punctured input counts all exact-error strata together.
No partition or varying-own-radius premise is hidden in these consumers. -/
namespace K1_2.Mixed
noncomputable section
open Finset
open scoped BigOperators
variable {α σ : Type*} [DecidableEq α] [DecidableEq σ]
local instance decShared (P : Prop) : Decidable P := Classical.propDecidable P

/-- The child bound is for the UNION of parent slopes incident to a
fixed removed set. Exact-error weight may vary with the parent slope. -/
theorem shared_child_incidence (D : Finset α) (Γ : Finset σ)
    (incident : α → σ → Prop) (beta child : ℕ)
    (hparent : ∀ γ∈Γ,beta ≤ (D.filter (fun I => incident I γ)).card)
    (hchild : ∀ I∈D,(Γ.filter (fun γ => incident I γ)).card ≤ child) :
    beta*Γ.card ≤ D.card*child := by
  classical
  have hswap : (∑ γ∈Γ,(D.filter (fun I => incident I γ)).card) =
      ∑ I∈D,(Γ.filter (fun γ => incident I γ)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  calc
    beta*Γ.card = ∑ _γ∈Γ,beta := by simp [Nat.mul_comm]
    _ ≤ ∑ γ∈Γ,(D.filter (fun I => incident I γ)).card := sum_le_sum hparent
    _ = ∑ I∈D,(Γ.filter (fun γ => incident I γ)).card := hswap
    _ ≤ ∑ _I∈D,child := sum_le_sum hchild
    _ = D.card*child := by simp

theorem shared_removed_set_incidence (nodes : Finset α) (Γ : Finset σ)
    (d beta child : ℕ) (incident : Finset α → σ → Prop)
    (hparent : ∀ γ∈Γ,beta ≤
      ((nodes.powersetCard d).filter (fun I => incident I γ)).card)
    (hchild : ∀ I∈nodes.powersetCard d,
      (Γ.filter (fun γ => incident I γ)).card ≤ child) :
    beta*Γ.card ≤ nodes.card.choose d*child := by
  simpa only [card_powersetCard] using
    shared_child_incidence (nodes.powersetCard d) Γ incident beta child hparent hchild

/-- Multiplying by a denominator preserves a RATIONAL child price,
avoiding a separate ceiling per removed set. -/
theorem shared_child_rational_incidence (D : Finset α) (Γ : Finset σ)
    (incident : α → σ → Prop) (beta numerator denominator : ℕ)
    (hparent : ∀ γ∈Γ,beta ≤ (D.filter (fun I => incident I γ)).card)
    (hchild : ∀ I∈D,denominator*(Γ.filter (fun γ => incident I γ)).card ≤ numerator) :
    denominator*beta*Γ.card ≤ D.card*numerator := by
  classical
  have hswap : (∑ γ∈Γ,(D.filter (fun I => incident I γ)).card) =
      ∑ I∈D,(Γ.filter (fun γ => incident I γ)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  have hlow : beta*Γ.card ≤ ∑ γ∈Γ,(D.filter (fun I => incident I γ)).card := by
    calc
      beta*Γ.card = ∑ _γ∈Γ,beta := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hparent
  calc
    denominator*beta*Γ.card = denominator*(beta*Γ.card) := by ring
    _ ≤ denominator*(∑ γ∈Γ,(D.filter (fun I => incident I γ)).card) :=
      Nat.mul_le_mul_left denominator hlow
    _ = ∑ I∈D,denominator*(Γ.filter (fun γ => incident I γ)).card := by
      rw [hswap,mul_sum]
    _ ≤ ∑ _I∈D,numerator := sum_le_sum hchild
    _ = D.card*numerator := by simp

end
end K1_2.Mixed
end PackSource_K1_2SharedIncidence

section PackSource_K1_2BetaMinimum
set_option autoImplicit true
set_option autoImplicit false

namespace K1_2.Mixed
open Nat

def deletionBeta (T A v c u : ℕ) : ℕ :=
  (T-u).choose (v-u+c)*(A+u-1).choose (u+c)

/-- The product, rather than every consecutive ratio, is bounded below
by its u=0 value. No native finite enumeration is used. -/
theorem deletionBeta_zero_le (T A v c u : ℕ) (hAT : T≤A)
    (hu : u≤v) (hfit : v+c≤T) :
    deletionBeta T A v c 0 ≤ deletionBeta T A v c u := by
  by_cases hu0 : u=0
  · subst u; rfl
  have huT : u≤T := by omega
  have hA : 0<A := by omega
  have hm1 : (T.choose u)*(u+c).choose u > 0 :=
    Nat.mul_pos (Nat.choose_pos huT) (Nat.choose_pos (by omega))
  have hcmp1 : (u+c).choose u ≤ (v+c).choose u :=
    Nat.choose_le_choose u (by omega)
  have hcmp2 : T.choose u ≤ (A+u-1).choose u :=
    Nat.choose_le_choose u (by omega)
  have hT := Nat.choose_mul (n:=T) (k:=v+c) (s:=u) (by omega)
  have hB := Nat.choose_mul (n:=A+u-1) (k:=u+c) (s:=u) (by omega)
  have he1 : v+c-u=v-u+c := by omega
  have he2 : A+u-1-u=A-1 := by omega
  have he3 : u+c-u=c := by omega
  rw [he1] at hT
  rw [he2,he3] at hB
  apply Nat.le_of_mul_le_mul_right (c := (T.choose u)*(u+c).choose u) ?_ hm1
  calc
    deletionBeta T A v c 0*((T.choose u)*(u+c).choose u) ≤
        deletionBeta T A v c 0*((v+c).choose u*(A+u-1).choose u) :=
      Nat.mul_le_mul_left _ (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hcmp1 hcmp2)
    _ = deletionBeta T A v c u*((T.choose u)*(u+c).choose u) := by
      simp only [deletionBeta,Nat.sub_zero,Nat.add_zero,Nat.zero_add]
      calc
        T.choose (v+c)*(A-1).choose c*((v+c).choose u*(A+u-1).choose u) =
            (T.choose (v+c)*(v+c).choose u)*
              ((A+u-1).choose u*(A-1).choose c) := by ring
        _ = (T.choose u*(T-u).choose (v-u+c))*
              ((A+u-1).choose (u+c)*(u+c).choose u) := by rw [hT,←hB]
        _ = _ := by ring

end K1_2.Mixed
end PackSource_K1_2BetaMinimum

section PackSource_K1_11_3Multiplicity
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11_3
noncomputable section
open Polynomial

/-- Multiple roots after SPECIALIZATION are assigned to one of at most B
ordinary Y derivatives. Generic squarefreeness is unnecessary. -/
theorem exists_simple_derivative_at_root {R : Type*} [CommRing R] [IsDomain R]
    (p B : ℕ) [CharP R p] (f : R[X]) (hf : f≠0) (hdegree : f.natDegree≤B)
    (hsmall : B<p) (y : R) (hroot : f.IsRoot y) :
    ∃ j<B,(derivative^[j] f).IsRoot y ∧ ¬(derivative (derivative^[j] f)).IsRoot y := by
  let μ := f.rootMultiplicity y
  have hμpos : 0<μ := (rootMultiplicity_pos hf).mpr hroot
  have hμle : μ≤B := by
    have hd := natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd y) hf
    have hle : μ≤f.natDegree := by simpa [μ,natDegree_pow] using hd
    exact hle.trans hdegree
  have hnzd : ∀ m≤μ,m≠0 → (m : R)∈nonZeroDivisors R := by
    intro m hm hmn
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    have hd : p∣m := (CharP.cast_eq_zero_iff R p m).mp hz
    have hp : p≤m := Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hd
    omega
  have hnext : ¬(derivative^[μ] f).IsRoot y := by
    intro hnext
    have hall : ∀ m≤μ,(derivative^[m] f).IsRoot y := by
      intro m hm
      rcases lt_or_eq_of_le hm with hh | rfl
      · exact isRoot_iterate_derivative_of_lt_rootMultiplicity hh
      · exact hnext
    have hc := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hf hall hnzd
    exact (Nat.lt_irrefl μ) hc
  refine ⟨μ-1,by omega,isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega),?_⟩
  have he : derivative (derivative^[μ-1] f)=derivative^[μ] f := by
    simpa only [Nat.succ_eq_add_one,Nat.sub_add_cancel hμpos] using (Function.iterate_succ_apply' derivative (μ-1) f).symm
  rwa [he]

end
end K1_11_3
end PackSource_K1_11_3Multiplicity

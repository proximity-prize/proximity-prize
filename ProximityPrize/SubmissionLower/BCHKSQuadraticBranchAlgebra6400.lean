import ProximityPrize.SubmissionLower.BCHKSQuadraticSquarefreeAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSQuadraticBranchAlgebra6400

open Polynomial

/-!
Ring-level lemmas for the quadratic squarefree/branch route.  These are
independent of the still-missing squarefree-factor selection theorem.
-/

noncomputable def quadratic {A : Type*} [CommRing A] (c a b : A) :
    Polynomial A :=
  Polynomial.C c * Polynomial.X ^ 2 +
    Polynomial.C a * Polynomial.X + Polynomial.C b

def quadraticDiscriminant {A : Type*} [CommRing A] (c a b : A) : A :=
  a ^ 2 - 4 * c * b

@[simp]
lemma eval_quadratic {A : Type*} [CommRing A] (c a b p : A) :
    Polynomial.eval p (quadratic c a b) = c * p ^ 2 + a * p + b := by
  simp [quadratic]

/-- A root of a quadratic makes its discriminant a square. -/
theorem quadraticDiscriminant_eq_square_of_root
    {A : Type*} [CommRing A] (c a b p : A)
    (hroot : c * p ^ 2 + a * p + b = 0) :
    quadraticDiscriminant c a b = (a + 2 * c * p) ^ 2 := by
  unfold quadraticDiscriminant
  calc
    a ^ 2 - 4 * c * b =
        (a + 2 * c * p) ^ 2 - 4 * c * (c * p ^ 2 + a * p + b) := by ring
    _ = (a + 2 * c * p) ^ 2 := by rw [hroot]; ring

theorem quadraticDiscriminant_eq_square_of_eval_root
    {A : Type*} [CommRing A] (c a b p : A)
    (hroot : Polynomial.eval p (quadratic c a b) = 0) :
    quadraticDiscriminant c a b = (a + 2 * c * p) ^ 2 := by
  apply quadraticDiscriminant_eq_square_of_root
  simpa using hroot

/-- Once the discriminant is a fixed square in a domain, every quadratic
root has one of the two global signs. -/
theorem quadratic_root_has_global_sign
    {A : Type*} [CommRing A] [IsDomain A]
    (c a b p h : A)
    (hroot : c * p ^ 2 + a * p + b = 0)
    (hdisc : quadraticDiscriminant c a b = h ^ 2) :
    a + 2 * c * p = h ∨ a + 2 * c * p = -h := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [← hdisc]
  exact (quadraticDiscriminant_eq_square_of_root c a b p hroot).symm

/-- Matching global signs give the same branch whenever `2c` is nonzero. -/
theorem eq_of_quadratic_branch_sign_eq
    {A : Type*} [CommRing A] [IsDomain A]
    (c a p u h : A) (htwo : (2 : A) ≠ 0) (hc : c ≠ 0)
    (hp : a + 2 * c * p = h) (hu : a + 2 * c * u = h) :
    p = u := by
  have heq : 2 * c * p = 2 * c * u := by
    exact add_left_cancel (hp.trans hu.symm)
  have hscale : (2 : A) * c ≠ 0 := mul_ne_zero htwo hc
  apply mul_left_cancel₀ hscale
  simpa [mul_assoc] using heq

/-- More points than the `X` degree ensure that a nonzero prospective square
factor is nonzero on at least one identity coordinate. -/
theorem exists_eval_ne_zero_of_natDegree_lt_card
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (I : Finset ι) (omega : ι → A) (B : Polynomial A)
    (homega : Function.Injective omega) (hB : B ≠ 0)
    (hcard : B.natDegree < I.card) :
    ∃ i ∈ I, Polynomial.eval (omega i) B ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero : B = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (ι := ↥I) B
      (homega.comp Subtype.val_injective)
      (fun i => hnone i.1 i.2)
      (by simpa using hcard)
  exact hB hzero

/-- `k+1` common evaluations determine a degree-`k` polynomial and hence
turn a fixed branch into an affine challenge line. -/
theorem polynomial_eq_affine_of_kplus_evaluations
    {F ι : Type*} [Field F] [DecidableEq ι]
    (I : Finset ι) (omega : ι → F) (k : ℕ)
    (P P0 P1 : Polynomial F) (z : F)
    (homega : Function.Injective omega)
    (hcard : k + 1 ≤ I.card)
    (hP : P.natDegree ≤ k)
    (hP0 : P0.natDegree ≤ k) (hP1 : P1.natDegree ≤ k)
    (heval : ∀ i ∈ I,
      Polynomial.eval (omega i) P =
        Polynomial.eval (omega i) (P0 + Polynomial.C z * P1)) :
    P = P0 + Polynomial.C z * P1 := by
  let rhs := P0 + Polynomial.C z * P1
  have hrhs : rhs.natDegree ≤ k := by
    dsimp [rhs]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le hP0 ((Polynomial.natDegree_C_mul_le z P1).trans hP1))
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P rhs
    (f := fun i : ↥I => omega i.1)
  · exact homega.comp Subtype.val_injective
  · intro i
    exact heval i.1 i.2
  · rw [Fintype.card_coe]
    exact (max_le hP hrhs).trans_lt (by omega)

end BCHKSQuadraticBranchAlgebra6400
end ProximityPrize.SubmissionLower

import ProximityPrize.SubmissionLower.BCHKSSubstitutionVanish
import ProximityPrize.SubmissionLower.BCHKSWeightedAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSWeightedSubstitution

open BCHKSSubstitutionVanish

/-!
The root-counting half of a coordinate-weighted Guruswami--Sudan
interpolant.  This file is deliberately conditional: it proves exactly what a
multiplicity assignment has to buy after interpolation, but it does not assume
that such an assignment exists for every agreement hypergraph.
-/

/-- Distinct roots with coordinate-dependent lower bounds consume the sum of
those bounds in the degree of the polynomial. -/
theorem sum_le_natDegree_of_rootMultiplicity
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial F) (ω : ι ↪ F) (A : Finset ι) (μ : ι → ℕ)
    (hmult : ∀ i ∈ A, μ i ≤ R.rootMultiplicity (ω i)) :
    ∑ i ∈ A, μ i ≤ R.natDegree := by
  let xs : Finset F := A.map ω
  have hselected :
      ∑ x ∈ xs, Multiset.count x R.roots ≤ R.roots.card := by
    let all := xs ∪ R.roots.toFinset
    calc
      ∑ x ∈ xs, Multiset.count x R.roots ≤
          ∑ x ∈ all, Multiset.count x R.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
      _ = ∑ x ∈ R.roots.toFinset, Multiset.count x R.roots := by
        symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro x hxall hxroots
        exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
      _ = R.roots.card := Multiset.toFinset_sum_count_eq R.roots
  calc
    ∑ i ∈ A, μ i ≤ ∑ i ∈ A, R.rootMultiplicity (ω i) :=
      Finset.sum_le_sum fun i hi => hmult i hi
    _ = ∑ x ∈ xs, R.rootMultiplicity x := by
      symm
      exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
    _ = ∑ x ∈ xs, Multiset.count x R.roots := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Polynomial.count_roots R).symm
    _ ≤ R.roots.card := hselected
    _ ≤ R.natDegree := Polynomial.card_roots' R

/-- Weighted GS substitution step.  Each matched coordinate may supply its
own vanishing order.  If their total reaches `DX`, while the substituted
polynomial has degree strictly below `DX`, it must vanish identically. -/
theorem triEval_eq_zero_of_weighted_shift_vanishing
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (ω : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F) (μ : ι → ℕ) (DX : ℕ)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < μ i →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (ω i) P = Polynomial.eval z (yZ i))
    (hdegree : (triEval Q z P).natDegree < DX)
    (hmany : DX ≤ ∑ i ∈ A, μ i) :
    triEval Q z P = 0 := by
  by_contra hne
  have hmult : ∀ i ∈ A,
      μ i ≤ (triEval Q z P).rootMultiplicity (ω i) := by
    intro i hi
    exact rootMultiplicity_triEval_ge_of_shift_coeff_zero
      Q (ω i) z (yZ i) P (μ i) (hvan i hi) (hmatch i hi) hne
  have hrootdeg := sum_le_natDegree_of_rootMultiplicity
    (triEval Q z P) ω A μ hmult
  omega

/-- A strict weighted `X`-support cap gives the strict degree inequality used
by weighted root counting. -/
theorem triEval_natDegree_lt_of_weighted_X_cap
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F)
    (k DX : ℕ) (hDX : 0 < DX) (hP : P.natDegree ≤ k)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 → a + k * j < DX) :
    (triEval Q z P).natDegree < DX := by
  have hle : (triEval Q z P).natDegree ≤ DX - 1 :=
    triEval_natDegree_le_of_weighted_X_cap Q z P k (DX - 1) hP (by
      intro j a hcoeff
      have := hcap j a hcoeff
      omega)
  omega

/-- Fully support-level weighted substitution theorem.  This is the weakest
root-side interface needed from a nonuniform interpolant: strict `X` support,
coordinatewise order-`μ i` vanishing, and a row sum at least `DX`. -/
theorem triEval_eq_zero_of_weighted_shift_vanishing_of_weighted_X_cap
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (ω : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F) (μ : ι → ℕ) (k DX : ℕ)
    (hDX : 0 < DX)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < μ i →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (ω i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ k)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 → a + k * j < DX)
    (hmany : DX ≤ ∑ i ∈ A, μ i) :
    triEval Q z P = 0 := by
  exact triEval_eq_zero_of_weighted_shift_vanishing Q z P ω A yZ μ DX
    hvan hmatch
    (triEval_natDegree_lt_of_weighted_X_cap Q z P k DX hDX hP hcap)
    hmany

end BCHKSWeightedSubstitution
end ProximityPrize.SubmissionLower

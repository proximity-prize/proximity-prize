import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import ProximityPrize.SubmissionLower.Koala6831SeedEncoding

namespace ProximityPrize.SubmissionLower.Koala6831BivariateSeeds

open Polynomial Koala6831SeedEncoding
open scoped Classical BigOperators

variable {K : Type*} [Field K] {b c : ℕ}

abbrev SeedPolynomial (K : Type*) [Field K] := MvPolynomial (Fin 2) K

def coordinates {R : Type*} (z₀ z₁ : R) (i : Fin 2) : R :=
  if i = 0 then z₀ else z₁

private noncomputable def seedExponent (i : SeedIndex b c) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.1.val + Finsupp.single 1 i.2.val

@[simp] private theorem seedExponent_zero (i : SeedIndex b c) :
    seedExponent i 0 = i.1.val := by
  simp [seedExponent]

@[simp] private theorem seedExponent_one (i : SeedIndex b c) :
    seedExponent i 1 = i.2.val := by
  simp [seedExponent]

private theorem seedExponent_injective :
    Function.Injective (seedExponent : SeedIndex b c → Fin 2 →₀ ℕ) := by
  intro i j h
  exact Prod.ext (Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 0) h))
    (Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h))

noncomputable def coefficients (P : SeedPolynomial K) (i : SeedIndex b c) : K :=
  P.coeff (seedExponent i)

private noncomputable def reconstruct (a : SeedIndex b c → K) : SeedPolynomial K :=
  ∑ i, MvPolynomial.monomial (seedExponent i) (a i)

private theorem coeff_reconstruct (a : SeedIndex b c → K) (i : SeedIndex b c) :
    (reconstruct a).coeff (seedExponent i) = a i := by
  rw [reconstruct, MvPolynomial.coeff_sum]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    have hne : seedExponent j ≠ seedExponent i := fun h => hji (seedExponent_injective h)
    simp [MvPolynomial.coeff_monomial, hne]
  · simp
  · simp

private theorem reconstruct_coefficients (P : SeedPolynomial K)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    reconstruct (coefficients (b := b) (c := c) P) = P := by
  apply MvPolynomial.ext
  intro d
  by_cases h : ∃ i : SeedIndex b c, seedExponent i = d
  · obtain ⟨i, rfl⟩ := h
    exact coeff_reconstruct (coefficients P) i
  · have hz : P.coeff d = 0 := by
      by_contra hne
      have hd := MvPolynomial.mem_support_iff.mpr hne
      let i : SeedIndex b c :=
        (⟨d 0, (MvPolynomial.monomial_le_degreeOf 0 hd).trans_lt h₀⟩,
         ⟨d 1, (MvPolynomial.monomial_le_degreeOf 1 hd).trans_lt h₁⟩)
      apply h
      refine ⟨i, Finsupp.ext ?_⟩
      rw [Fin.forall_fin_two]
      simp [i]
    rw [hz, reconstruct, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hne : seedExponent i ≠ d := fun heq => h ⟨i, heq⟩
    simp [MvPolynomial.coeff_monomial, hne]

theorem coefficients_nonzero {P : SeedPolynomial K} (hP : P ≠ 0)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    coefficients (b := b) (c := c) P ≠ 0 := by
  intro hz
  apply hP
  calc
    P = reconstruct (coefficients (b := b) (c := c) P) :=
      (reconstruct_coefficients P h₀ h₁).symm
    _ = 0 := by simp [hz, reconstruct]

noncomputable def frobeniusHom (p : ℕ) : SeedPolynomial K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (coordinates Polynomial.X (Polynomial.X ^ p))

theorem eval_frobeniusHom (p : ℕ) (P : SeedPolynomial K) (g : K) :
    (frobeniusHom p P).eval g = MvPolynomial.eval (coordinates g (g ^ p)) P := by
  change ((Polynomial.evalRingHom g).comp (frobeniusHom p)) P = _
  unfold frobeniusHom MvPolynomial.eval
  rw [MvPolynomial.comp_eval₂Hom]
  have hC : (Polynomial.evalRingHom g).comp (Polynomial.C : K →+* K[X]) = RingHom.id K := by
    apply RingHom.ext
    intro a
    simp
  have hpoint : (fun i => Polynomial.evalRingHom g
      (coordinates Polynomial.X (Polynomial.X ^ p) i)) = coordinates g (g ^ p) := by
    funext i
    by_cases hi : i = 0 <;> simp [coordinates, hi, map_pow]
  rw [hC, hpoint]

theorem frobeniusHom_eq_encode (p : ℕ) (P : SeedPolynomial K)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    frobeniusHom p P = encode p (coefficients (b := b) (c := c) P) := by
  calc
    frobeniusHom p P = frobeniusHom p (reconstruct (coefficients (b := b) (c := c) P)) :=
      congrArg (frobeniusHom p) (reconstruct_coefficients P h₀ h₁).symm
    _ = encode p (coefficients (b := b) (c := c) P) := by
      rw [reconstruct, encode, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [frobeniusHom, MvPolynomial.eval₂Hom_monomial,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      simp [coordinates, exponent, pow_add, pow_mul]

theorem frobeniusHom_nonzero {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    {P : SeedPolynomial K} (hP : P ≠ 0) (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    frobeniusHom p P ≠ 0 := by
  rw [frobeniusHom_eq_encode p P h₀ h₁]
  exact encode_nonzero hp hb (coefficients_nonzero hP h₀ h₁)

theorem natDegree_frobeniusHom_le (p : ℕ) (P : SeedPolynomial K)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    (frobeniusHom p P).natDegree ≤ (b - 1) + p * (c - 1) := by
  rw [frobeniusHom_eq_encode p P h₀ h₁]
  exact natDegree_encode_le p _

theorem card_le_of_vanishing {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    {P : SeedPolynomial K} (hP : P ≠ 0) (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c)
    (seeds : Finset K) (hzero : ∀ g ∈ seeds, MvPolynomial.eval (coordinates g (g ^ p)) P = 0) :
    seeds.card ≤ (b - 1) + p * (c - 1) := by
  have hcard : seeds.card ≤ (frobeniusHom p P).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    exact (Polynomial.mem_roots (frobeniusHom_nonzero hp hb hP h₀ h₁)).mpr
      ((eval_frobeniusHom p P g).trans (hzero g hg))
  exact hcard.trans (natDegree_frobeniusHom_le p P h₀ h₁)

end ProximityPrize.SubmissionLower.Koala6831BivariateSeeds

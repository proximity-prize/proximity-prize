/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from Lucieno's comparison and Bome2017's 68.31
joint-incidence tightening. Changes keep the primary and secondary heights separate.
The 68.32 release contains the original implementations. -/
import ProximityPrize.SubmissionLower.Koala6831RankTwo
import Mathlib.Tactic
namespace ProximityPrize.SubmissionLower.Frontier6969Mixed
open Koala6831Comparison Koala6831CramerIncidence Koala6831BivariateSeeds
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
private theorem coefficient_degree_mul (f g : Polynomial (Polynomial K)) (b c : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ b) (hg : ∀ j, (g.coeff j).natDegree ≤ c) :
    ∀ j, ((f * g).coeff j).natDegree ≤ b + c := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hf ij.1) (hg ij.2))

omit [DecidableEq K] in
private theorem coefficient_degree_sub (f g : Polynomial (Polynomial K)) (b : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ b) (hg : ∀ j, (g.coeff j).natDegree ≤ b) :
    ∀ j, ((f - g).coeff j).natDegree ≤ b := by
  intro j
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hf j) (hg j))

theorem two_mixed_rows {d₀ d₁ p : ℕ} (hp : 0 < p)
    (x : I ↪ K) (u₀ u₁ : I → K) (selected secondValue : K → Polynomial K)
    (row₀ : EncodedRow K d₀ p) (row₁ : EncodedRow K d₁ p)
    (hnonzero : row₀.first * row₁.second - row₀.second * row₁.first ≠ 0)
    (seeds : Finset K) (nodes : Finset I) (w a e : ℕ)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      a ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (h₀ : ∀ g ∈ seeds, row₀.satisfied g (selected g) (secondValue g))
    (h₁ : ∀ g ∈ seeds, row₁.satisfied g (selected g) (secondValue g))
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - JointIdentity.splitPoint w a) * ((d₀+d₁ + 2) * (p + 1)) / (a - JointIdentity.splitPoint w a))
      (nodes.card * ((d₀+d₁ + 1) * (p + 1)) / (JointIdentity.tolerance w a + 1) + (e + 1)) := by
  let denominator := row₀.first * row₁.second - row₀.second * row₁.first
  let numerator := row₀.second * row₁.beta - row₀.beta * row₁.second
  let denCap := (d₀+d₁ + 1) * (p + 1)
  let numCap := (d₀+d₁ + 2) * (p + 1)
  have hD : ∀ j, (denominator.coeff j).natDegree ≤ denCap := by
    apply coefficient_degree_sub
    · intro j
      have h := coefficient_degree_mul row₀.first row₁.second _ _ row₀.firstCap row₁.secondCap j
      exact h.trans_eq (by dsimp [denCap]; ring)
    · intro j
      have h := coefficient_degree_mul row₀.second row₁.first _ _ row₀.secondCap row₁.firstCap j
      exact h.trans_eq (by dsimp [denCap]; ring)
  have hN : ∀ j, (numerator.coeff j).natDegree ≤ numCap := by
    apply coefficient_degree_sub
    · intro j
      have h := coefficient_degree_mul row₀.second row₁.beta _ _ row₀.secondCap row₁.betaCap j
      have hcompare : (d₀ + 1) + p * d₀ + ((d₁ + 1) + p * (d₁ + 1)) + p = numCap := by
        dsimp [numCap]
        ring
      exact h.trans (by omega)
    · intro j
      have h := coefficient_degree_mul row₀.beta row₁.second _ _ row₀.betaCap row₁.secondCap j
      have hcompare : (d₀ + 1) + p * (d₀ + 1) + ((d₁ + 1) + p * d₁) + p = numCap := by
        dsimp [numCap]
        ring
      exact h.trans (by omega)
  have hEq : ∀ g ∈ seeds, denominator.map (Polynomial.evalRingHom g) * selected g =
      numerator.map (Polynomial.evalRingHom g) := by
    intro g hg
    simp only [denominator, numerator, Polynomial.map_sub, Polynomial.map_mul]
    exact first_coordinate_cramer _ _ _ _ _ _ _ _ (h₀ g hg) (h₁ g hg)
  have hmax : max numCap (denCap + 1) = numCap := by
    apply max_eq_left
    have hstep : denCap + (p + 1) = numCap := by dsimp [denCap, numCap]; ring
    omega
  simpa only [hmax, denCap, numCap] using
    encoded_chart_bound x u₀ u₁ selected denominator numerator hnonzero seeds nodes
      w a e denCap numCap hwa han hdegree hagreement hD hN hEq hpencil

end
end ProximityPrize.SubmissionLower.Frontier6969Mixed

namespace ProximityPrize.SubmissionLower.Frontier6969Mixed

open Koala6831Comparison Koala6831CramerIncidence Koala6831BivariateSeeds
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

private def encodeRow {A a d D : ℕ} (θ : RowIndex A a d → K) (p : ℕ)
    (hle : d ≤ D) : EncodedRow K D p where
  beta := (symbolicRow θ).beta.map (frobeniusHom p)
  first := (symbolicRow θ).first.map (frobeniusHom p)
  second := (symbolicRow θ).second.map (frobeniusHom p)
  betaCap j := by
    rw [Polynomial.coeff_map]
    have h := (symbolicRow_seed_degree_bounds θ j).1
    exact (natDegree_frobeniusHom_le (b := d + 2) (c := d + 2) p _
      (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans
      (Nat.add_le_add (Nat.succ_le_succ hle) (Nat.mul_le_mul_left p (Nat.succ_le_succ hle)))
  firstCap j := by
    rw [Polynomial.coeff_map]
    have h := (symbolicRow_seed_degree_bounds θ j).2.1
    exact (natDegree_frobeniusHom_le (b := d + 1) (c := d + 2) p _
      (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans
      (Nat.add_le_add hle (Nat.mul_le_mul_left p (Nat.succ_le_succ hle)))
  secondCap j := by
    rw [Polynomial.coeff_map]
    have h := (symbolicRow_seed_degree_bounds θ j).2.2
    exact (natDegree_frobeniusHom_le (b := d + 2) (c := d + 1) p _
      (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans
      (Nat.add_le_add (Nat.succ_le_succ hle) (Nat.mul_le_mul_left p hle))

private theorem map_frobenius_eval (F : Polynomial (SeedPolynomial K)) (p : ℕ) (g : K) :
    (F.map (frobeniusHom p)).map (Polynomial.evalRingHom g) =
      F.map (MvPolynomial.eval (coordinates g (g ^ p))) := by
  have hEval : (Polynomial.evalRingHom g).comp (frobeniusHom p) =
      MvPolynomial.eval (coordinates g (g ^ p)) := by
    apply RingHom.ext
    intro P
    exact eval_frobeniusHom p P g
  rw [Polynomial.map_map, hEval]

private theorem satisfied_of_specialize {A a d D : ℕ} (θ : RowIndex A a d → K)
    (p : ℕ) (hle : d ≤ D) (g : K) (P Q : Polynomial K)
    (h : let row := specialize θ (g, g ^ p)
      row.beta + row.first * P + row.second * Q = 0) : (encodeRow θ p hle).satisfied g P Q := by
  obtain ⟨hβ, h₀, h₁⟩ := symbolicRow_map_seedEval θ (coordinates g (g ^ p))
  dsimp only [EncodedRow.satisfied, encodeRow]
  rw [map_frobenius_eval, map_frobenius_eval, map_frobenius_eval, hβ, h₀, h₁]
  simpa [coordinates] using h

private theorem coefficient_bidegree_mul (F G : Polynomial (SeedPolynomial K))
    (i : Fin 2) (b c : ℕ) (hF : ∀ j, (F.coeff j).degreeOf i ≤ b)
    (hG : ∀ j, (G.coeff j).degreeOf i ≤ c) (j : ℕ) :
    ((F * G).coeff j).degreeOf i ≤ b + c := by
  rw [Polynomial.coeff_mul]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro index _
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (hF _) (hG _))

private theorem encoded_det_nonzero {A a d₀ d₁ D p : ℕ} (hp : 0 < p) (hwidth : 2*D + 2 ≤ p)
    (hle₀ : d₀ ≤ D) (hle₁ : d₁ ≤ D)
    (θ : RowIndex A a d₀ → K) (η : RowIndex A a d₁ → K)
    (hdet : (symbolicRow θ).first * (symbolicRow η).second -
      (symbolicRow θ).second * (symbolicRow η).first ≠ 0) :
    (encodeRow θ p (le_refl _)).first * (encodeRow η p (le_refl _)).second -
      (encodeRow θ p (le_refl _)).second * (encodeRow η p (le_refl _)).first ≠ 0 := by
  let δ := (symbolicRow θ).first * (symbolicRow η).second -
      (symbolicRow θ).second * (symbolicRow η).first
  have hDegree₀ (j : ℕ) : (δ.coeff j).degreeOf 0 ≤ 2*D + 1 := by
    dsimp only [δ]
    rw [Polynomial.coeff_sub]
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (coefficient_bidegree_mul _ _ 0 d₀ (d₁+1)
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.1.1)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.2.1) j).trans (by omega)
    · refine (coefficient_bidegree_mul _ _ 0 (d₀+1) d₁
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.2.1)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.1.1) j).trans (by omega)
  have hDegree₁ (j : ℕ) : (δ.coeff j).degreeOf 1 ≤ 2*D + 1 := by
    dsimp only [δ]
    rw [Polynomial.coeff_sub]
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (coefficient_bidegree_mul _ _ 1 (d₀+1) d₁
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.1.2)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.2.2) j).trans (by omega)
    · refine (coefficient_bidegree_mul _ _ 1 d₀ (d₁+1)
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.2.2)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.1.2) j).trans (by omega)
  have hmap : δ.map (frobeniusHom p) ≠ 0 := by
    intro hz
    apply hdet
    change δ = 0
    apply Polynomial.ext
    intro j
    simp only [Polynomial.coeff_zero]
    by_contra hne
    have hDegree₀' : (δ.coeff j).degreeOf 0 < 2*D + 2 := by
      have := hDegree₀ j
      omega
    have hDegree₁' : (δ.coeff j).degreeOf 1 < 2*D + 2 := by
      have := hDegree₁ j
      omega
    apply frobeniusHom_nonzero hp hwidth hne hDegree₀' hDegree₁'
    have hcoeff := congrArg (fun f : Polynomial (Polynomial K) => f.coeff j) hz
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hcoeff
  simpa only [δ, Polynomial.map_sub, Polynomial.map_mul, encodeRow] using hmap

theorem actual_rows {I : Type} [Fintype I]
    {A a d₀ d₁ D p w e : ℕ} (hp : 0 < p) (hwidth : 2*D + 2 ≤ p)
    (hle₀ : d₀ ≤ D) (hle₁ : d₁ ≤ D)
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (haPos : 0 < a) (ha : a + w = A) (han : A ≤ Fintype.card I)
    (θ : ComparisonSpace A a d₀ x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (η : ComparisonSpace A a d₁ x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (hdet : (symbolicRow θ.1).first * (symbolicRow η.1).second -
      (symbolicRow θ.1).second * (symbolicRow η.1).first ≠ 0)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (Finset.univ.filter (fun i => (selected g).eval (x i) = U 0 i + g * U 1 i)).card)
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max ((Fintype.card I - JointIdentity.splitPoint w A) * ((d₀+d₁ + 2) * (p + 1)) / (A - JointIdentity.splitPoint w A))
      (Fintype.card I * ((d₀+d₁ + 1) * (p + 1)) / (JointIdentity.tolerance w A + 1) + (e + 1)) := by
  rw [← Finset.card_univ (α := I)]
  apply two_mixed_rows hp x (U 0) (U 1) selected (fun g => (selected g).map σ)
    (encodeRow θ.1 p (le_refl _)) (encodeRow η.1 p (le_refl _))
    (encoded_det_nonzero hp hwidth hle₀ hle₁ θ.1 η.1 hdet)
    seeds Finset.univ w A e (by omega) (by simpa using han) hdegree hagreement
  · intro g hg
    apply satisfied_of_specialize
    rw [← hσ g]
    exact specialize_selected_eq_zero x U σ hfixed haPos ha θ g (selected g) (hdegree g hg)
      _ (hagreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)
  · intro g hg
    apply satisfied_of_specialize
    rw [← hσ g]
    exact specialize_selected_eq_zero x U σ hfixed haPos ha η g (selected g) (hdegree g hg)
      _ (hagreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)
  · exact hpencil

#print axioms actual_rows

end

end ProximityPrize.SubmissionLower.Frontier6969Mixed

/- Modified for this joint-incidence adaptation of Lucieno’s PR 618, November 2026. -/

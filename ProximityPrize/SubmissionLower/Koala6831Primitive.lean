import Mathlib.RingTheory.Polynomial.UniqueFactorization
import ProximityPrize.SubmissionLower.Koala6831PrimitiveBoxes
import ProximityPrize.SubmissionLower.Koala6831ComparisonRank

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open Polynomial
open scoped BigOperators

noncomputable section

variable {K I : Type*} [Field K]

abbrev SeedCoefficients (K : Type*) [Field K] := Polynomial (SeedRing K)

def rankRow {A a d : ℕ} (θ : RowIndex A a d → K) : SymbolicRow (SeedRing K) :=
  let q := symbolicRow θ
  ⟨q.beta, q.first, q.second⟩

private theorem symbolicRow_ext {R : Type*} [CommRing R] {q r : SymbolicRow R}
    (hb : q.beta = r.beta) (h₀ : q.first = r.first) (h₁ : q.second = r.second) : q = r := by
  cases q
  cases r
  simp_all

theorem rankRow_injective (A a d : ℕ) :
    Function.Injective (rankRow : (RowIndex A a d → K) → SymbolicRow (SeedRing K)) := by
  intro θ η h
  apply symbolicRow_injective A a d
  exact congrArg (fun r : SymbolicRow (SeedRing K) =>
    (⟨r.beta, r.first, r.second⟩ : SpecializedRow (SeedRing K))) h

theorem rankRow_degrees {A a d : ℕ} (θ : RowIndex A a d → K) :
    let q := rankRow θ
    q.beta.natDegree ≤ A - 1 ∧ q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
  specialize_degrees (fun j => MvPolynomial.C (θ j))
    (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))

def seedNode (x : I ↪ K) : I ↪ SeedRing K :=
  ⟨fun i => MvPolynomial.C (x i), (MvPolynomial.C_injective (Fin 2) K).comp x.injective⟩

def affineSeedWord (u v : Fin 2 → I → K) (j : Fin 2) (i : I) : SeedRing K :=
  MvPolynomial.C (u j i) + MvPolynomial.X j * MvPolynomial.C (v j i)

theorem rankRow_atNode_zero {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (θ : ComparisonSpace A a d x u v) (i : I) :
    (rankRow θ.1).atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i) = 0 := by
  exact symbolicRow_eval_received_eq_zero x u v θ i

private theorem rankRow_zero {A a d : ℕ} :
    rankRow (0 : RowIndex A a d → K) = ⟨0, 0, 0⟩ := by
  simp [rankRow, symbolicRow, specialize, specializePiece]

theorem rankRow_has_active_coefficient [Fintype I] {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (θ : ComparisonSpace A a d x u v)
    (hθ : θ.1 ≠ 0) (hA : A - 1 < Fintype.card I) :
    (rankRow θ.1).first ≠ 0 ∨ (rankRow θ.1).second ≠ 0 := by
  classical
  by_contra! hz
  have hb := beta_eq_zero_of_no_active_coefficient
    (rankRow θ.1) (seedNode x) Finset.univ
    (affineSeedWord u v 0) (affineSeedWord u v 1)
    ((rankRow_degrees θ.1).1.trans_lt (by simpa using hA))
    hz.1 hz.2 (fun i _ => rankRow_atNode_zero x u v θ i)
  apply hθ (rankRow_injective A a d ?_)
  rw [rankRow_zero]
  exact symbolicRow_ext hb hz.1 hz.2

structure RowFactors (q r : SymbolicRow (SeedRing K)) (m : SeedCoefficients K) : Prop where
  beta : r.beta = m * q.beta
  first : r.first = m * q.first
  second : r.second = m * q.second

def IsPrimitiveRow (q : SymbolicRow (SeedRing K)) : Prop :=
  ∀ f, f ∣ q.beta → f ∣ q.first → f ∣ q.second → IsUnit f

private def swapValueCoefficients (q : SymbolicRow (SeedRing K)) : SymbolicRow (SeedRing K) :=
  ⟨q.beta, q.second, q.first⟩

private theorem primitiveRow_from_unit_gcd [GCDMonoid (SeedCoefficients K)]
    (q : SymbolicRow (SeedRing K)) (h : IsUnit (gcd q.beta (gcd q.first q.second))) :
    IsPrimitiveRow q := by
  intro f hb h₀ h₁
  exact isUnit_of_dvd_unit (dvd_gcd hb (dvd_gcd h₀ h₁)) h

private theorem unit_gcd_from_primitiveRow [GCDMonoid (SeedCoefficients K)]
    (q : SymbolicRow (SeedRing K)) (h : IsPrimitiveRow q) :
    IsUnit (gcd q.beta (gcd q.first q.second)) :=
  h _ (gcd_dvd_left _ _) ((gcd_dvd_right _ _).trans (gcd_dvd_left _ _))
    ((gcd_dvd_right _ _).trans (gcd_dvd_right _ _))

theorem primitive_factor_of_active (r : SymbolicRow (SeedRing K))
    (h : r.first ≠ 0 ∨ r.second ≠ 0) :
    ∃ (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K), m ≠ 0 ∧
      (q.first ≠ 0 ∨ q.second ≠ 0) ∧ IsPrimitiveRow q ∧ RowFactors q r m := by
  let _ : NormalizedGCDMonoid (SeedCoefficients K) := Classical.ofNonempty
  rcases h with h₀ | h₁
  · obtain ⟨q, m, hm, ha, hunit, hb, hf, hs⟩ := exists_primitive_factor_of_first_ne_zero r h₀
    exact ⟨q, m, hm, Or.inl ha, primitiveRow_from_unit_gcd q hunit, ⟨hb, hf, hs⟩⟩
  · obtain ⟨q, m, hm, ha, hunit, hb, hf, hs⟩ :=
      exists_primitive_factor_of_first_ne_zero (swapValueCoefficients r) h₁
    refine ⟨swapValueCoefficients q, m, hm, Or.inr ha, ?_, ⟨hb, hs, hf⟩⟩
    intro f hβ hfirst hsecond
    exact primitiveRow_from_unit_gcd q hunit f hβ hsecond hfirst

private theorem multiply_primitive_of_cross_eq (q r : SymbolicRow (SeedRing K))
    (hp : IsPrimitiveRow q) (ha : q.first ≠ 0 ∨ q.second ≠ 0)
    (hdet : q.first * r.second = r.first * q.second)
    (hb₀ : q.first * r.beta = r.first * q.beta)
    (hb₁ : q.second * r.beta = r.second * q.beta) :
    ∃ m : SeedCoefficients K, RowFactors q r m := by
  let _ : NormalizedGCDMonoid (SeedCoefficients K) := Classical.ofNonempty
  rcases ha with ha | ha
  · obtain ⟨m, hb, h₀, h₁⟩ :=
      exists_polynomial_multiplier_of_primitive_first q r ha
        (unit_gcd_from_primitiveRow q hp) hdet hb₀
    exact ⟨m, ⟨hb, h₀, h₁⟩⟩
  · have hps : IsPrimitiveRow (swapValueCoefficients q) := by
      intro f hb h₀ h₁
      exact hp f hb h₁ h₀
    have hdet' : (swapValueCoefficients q).first * (swapValueCoefficients r).second =
        (swapValueCoefficients r).first * (swapValueCoefficients q).second := by
      change q.second * r.first = r.second * q.first
      rw [mul_comm q.second, hdet.symm, mul_comm q.first]
    obtain ⟨m, hb, h₁, h₀⟩ :=
      exists_polynomial_multiplier_of_primitive_first (swapValueCoefficients q)
        (swapValueCoefficients r) ha (unit_gcd_from_primitiveRow _ hps) hdet' hb₁
    exact ⟨m, ⟨hb, h₀, h₁⟩⟩

private theorem cross_eq_of_mul_left {a b c d m : SeedCoefficients K}
    (hm : m ≠ 0) (h : (m * a) * b = c * (m * d)) : a * b = c * d := by
  apply mul_left_cancel₀ hm
  rw [← mul_assoc, h, mul_left_comm]

theorem exists_primitive_comparison_generator [Fintype I] {A a d₀ d₁ : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K)
    (θ₀ : ComparisonSpace A a d₀ x u v) (hθ₀ : θ₀.1 ≠ 0)
    (hbudget : (a - 1) + (A - 1) < Fintype.card I)
    (hcollinear : ∀ θ : ComparisonSpace A a d₁ x u v,
      (rankRow θ₀.1).first * (rankRow θ.1).second =
        (rankRow θ.1).first * (rankRow θ₀.1).second) :
    ∃ (q : SymbolicRow (SeedRing K)) (m₀ : SeedCoefficients K), m₀ ≠ 0 ∧
      (q.first ≠ 0 ∨ q.second ≠ 0) ∧ IsPrimitiveRow q ∧
      RowFactors q (rankRow θ₀.1) m₀ ∧
      ∀ θ : ComparisonSpace A a d₁ x u v, ∃ m, RowFactors q (rankRow θ.1) m := by
  classical
  obtain ⟨q, m, hm, ha, hp, hm₀⟩ := primitive_factor_of_active (rankRow θ₀.1)
    (rankRow_has_active_coefficient x u v θ₀ hθ₀ (by omega))
  refine ⟨q, m, hm, ha, hp, hm₀, fun θ => ?_⟩
  have hd₀ := rankRow_degrees θ₀.1
  have hd₁ := rankRow_degrees θ.1
  have ⟨hb₀, hb₁⟩ := cross_beta_eq_of_determinant_zero
    (seedNode x) Finset.univ (affineSeedWord u v 0) (affineSeedWord u v 1)
    (rankRow θ₀.1) (rankRow θ.1) (a - 1) (A - 1) (by simpa using hbudget)
    hd₀.2.1 hd₁.2.1 hd₀.2.2 hd₁.2.2 hd₀.1 hd₁.1
    (fun i _ => rankRow_atNode_zero x u v θ₀ i)
    (fun i _ => rankRow_atNode_zero x u v θ i) (hcollinear θ)
  apply multiply_primitive_of_cross_eq q (rankRow θ.1) hp ha
  · apply cross_eq_of_mul_left hm
    rw [← hm₀.first, ← hm₀.second]
    exact hcollinear θ
  · apply cross_eq_of_mul_left hm
    rw [← hm₀.first, ← hm₀.beta]
    exact hb₀
  · apply cross_eq_of_mul_left hm
    rw [← hm₀.second, ← hm₀.beta]
    exact hb₁

end

end ProximityPrize.SubmissionLower.Koala6831Comparison

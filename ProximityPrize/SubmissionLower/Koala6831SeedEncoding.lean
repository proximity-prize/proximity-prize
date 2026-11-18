import Mathlib.Algebra.Polynomial.Roots

namespace ProximityPrize.SubmissionLower.Koala6831SeedEncoding

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {b c : ℕ}

abbrev SeedIndex (b c : ℕ) := Fin b × Fin c

def exponent (p : ℕ) (index : SeedIndex b c) : ℕ :=
  index.1.val + p * index.2.val

theorem exponent_injective {p : ℕ} (hp : 0 < p) (hb : b ≤ p) :
    Function.Injective (exponent (b := b) (c := c) p) := by
  intro i j hij
  have hi := Nat.lt_of_lt_of_le i.1.isLt hb
  have hj := Nat.lt_of_lt_of_le j.1.isLt hb
  have hfirst : i.1.val = j.1.val := by
    simpa only [exponent, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      using congrArg (fun n : ℕ => n % p) hij
  have hmul : p * i.2.val = p * j.2.val := by
    apply Nat.add_left_cancel (n := j.1.val)
    simpa only [exponent, hfirst] using hij
  exact Prod.ext (Fin.ext hfirst) (Fin.ext (Nat.eq_of_mul_eq_mul_left hp hmul))

noncomputable def encode (p : ℕ) (a : SeedIndex b c → K) : K[X] :=
  ∑ index, monomial (exponent p index) (a index)

theorem coeff_encode {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    (a : SeedIndex b c → K) (index : SeedIndex b c) :
    (encode p a).coeff (exponent p index) = a index := by
  rw [encode, Polynomial.finsetSum_coeff]
  calc
    (∑ k, (monomial (exponent p k) (a k)).coeff (exponent p index)) =
        (monomial (exponent p index) (a index)).coeff (exponent p index) := by
      apply Finset.sum_eq_single index
      · intro k _ hk
        have hne : exponent p k ≠ exponent p index :=
          fun heq => hk (exponent_injective hp hb heq)
        simp [Polynomial.coeff_monomial, hne]
      · intro hnot
        exact (hnot (Finset.mem_univ index)).elim
    _ = a index := by simp

theorem encode_injective {p : ℕ} (hp : 0 < p) (hb : b ≤ p) :
    Function.Injective (encode (K := K) (b := b) (c := c) p) := by
  intro a a' heq
  funext index
  have hcoeff := congrArg (fun q : K[X] => q.coeff (exponent p index)) heq
  simpa only [coeff_encode hp hb] using hcoeff

@[simp] theorem encode_zero (p : ℕ) : encode (K := K) (b := b) (c := c) p 0 = 0 := by
  simp [encode]

theorem encode_nonzero {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    {a : SeedIndex b c → K} (ha : a ≠ 0) : encode p a ≠ 0 := by
  intro hz
  have heq : encode p a = encode p (0 : SeedIndex b c → K) := by
    simpa only [encode_zero] using hz
  exact ha (encode_injective hp hb heq)

theorem natDegree_encode_le (p : ℕ) (a : SeedIndex b c → K) :
    (encode p a).natDegree ≤ (b - 1) + p * (c - 1) := by
  unfold encode
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index _
  apply (Polynomial.natDegree_monomial_le (a index) (m := exponent p index)).trans
  have hfirst : index.1.val ≤ b - 1 := Nat.le_sub_one_of_lt index.1.isLt
  have hsecond : index.2.val ≤ c - 1 := Nat.le_sub_one_of_lt index.2.isLt
  exact Nat.add_le_add hfirst (Nat.mul_le_mul_left p hsecond)

end ProximityPrize.SubmissionLower.Koala6831SeedEncoding

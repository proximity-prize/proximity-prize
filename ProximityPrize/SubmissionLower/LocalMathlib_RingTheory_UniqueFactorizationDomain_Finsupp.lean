/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 9631fa2f9091797c1f6839159f70b61e4db4ee28df9ad43563576fcb21b5eb4a.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-!
# Factors as finsupp

## Main definitions
* `UniqueFactorizationMonoid.factorization`: the multiset of irreducible factors as a `Finsupp`.
-/

section ProximityFlatProofPort

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section Finsupp

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable [NormalizationMonoid α] [DecidableEq α]

open UniqueFactorizationMonoid

/-- This returns the multiset of irreducible factors as a `Finsupp`. -/
noncomputable def factorization (n : α) : α →₀ ℕ :=
  Multiset.toFinsupp (normalizedFactors n)

theorem factorization_eq_count {n p : α} :
    factorization n p = Multiset.count p (normalizedFactors n) := by simp [factorization]

@[simp]
theorem factorization_zero : factorization (0 : α) = 0 := by simp [factorization]

@[simp]
theorem factorization_one : factorization (1 : α) = 0 := by simp [factorization]

/-- The support of `factorization n` is exactly the Finset of normalized factors -/
@[simp]
theorem support_factorization {n : α} :
    (factorization n).support = (normalizedFactors n).toFinset := by
  simp [factorization, Multiset.toFinsupp_support]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
theorem factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    factorization (a * b) = factorization a + factorization b := by
  simp [factorization, normalizedFactors_mul ha hb]

/-- For any `p`, the power of `p` in `x^n` is `n` times the power in `x` -/
theorem factorization_pow {x : α} {n : ℕ} : factorization (x ^ n) = n • factorization x := by
  ext
  simp [factorization]

theorem associated_of_factorization_eq (a b : α) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : factorization a = factorization b) : Associated a b := by
  simp_rw [factorization, AddEquiv.apply_eq_iff_eq] at h
  rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]

end Finsupp

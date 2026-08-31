/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Johannes Hölzl,Jens Wagemaker,Aaron Anderson
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
variable {α:Type*}
local infixl:50 " ~ᵤ " => Associated
section Finsupp
variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable [NormalizationMonoid α] [DecidableEq α]
open UniqueFactorizationMonoid
noncomputable def factorization (n:α):α →₀ ℕ:=
  Multiset.toFinsupp (normalizedFactors n)
theorem factorization_eq_count {n p:α}:
    factorization n p=Multiset.count p (normalizedFactors n):=by simp [factorization]
@[simp]
theorem factorization_zero:factorization (0:α)=0:=by simp [factorization]
@[simp]
theorem factorization_one:factorization (1:α)=0:=by simp [factorization]
@[simp]
theorem support_factorization {n:α}:
    (factorization n).support=(normalizedFactors n).toFinset:=by
  simp [factorization,Multiset.toFinsupp_support]
@[simp]
theorem factorization_mul {a b:α} (ha:a≠0) (hb:b≠0):
    factorization (a*b)=factorization a+factorization b:=by
  simp [factorization,normalizedFactors_mul ha hb]
theorem factorization_pow {x:α} {n:ℕ}:factorization (x^n)=n • factorization x:=by
  ext
  simp [factorization]
theorem associated_of_factorization_eq (a b:α) (ha:a≠0) (hb:b≠0)
    (h:factorization a=factorization b):Associated a b:=by
  simp_rw [factorization,AddEquiv.apply_eq_iff_eq] at h
  rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]
end Finsupp

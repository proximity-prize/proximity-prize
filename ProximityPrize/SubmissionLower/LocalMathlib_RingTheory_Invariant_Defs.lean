/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Thomas Browning
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
namespace Algebra
variable (A B G:Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]
@[mk_iff] class IsInvariant:Prop where
  isInvariant:∀ b:B,(∀ g:G,g • b=b) → ∃ a:A,algebraMap A B a=b
end Algebra

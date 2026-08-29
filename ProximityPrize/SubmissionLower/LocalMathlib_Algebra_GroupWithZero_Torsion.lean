/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Xavier Roblot
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.Algebra.GroupWithZero.Torsion.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 690464d5bf13fce10a91bd15774810084d5d8435e35df2c33f8aaa3f21c54db0.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
Port elaboration adjustment: explicitly choose classical decidability in
the existing case-split proof; its statement and argument are unchanged.
-/

/-!
# Torsion-free monoids with zero

We prove that if `M` is an `UniqueFactorizationMonoid` that can be equipped with a
`NormalizationMonoid` structure and such that `Mˣ` is torsion-free, then `M` is torsion-free.

Note. You need to import this file to get that the monoid of ideals of a Dedekind domain is
torsion-free.
-/

section ProximityFlatProofPort

variable {M : Type*} [CommMonoidWithZero M]

theorem IsMulTorsionFree.mk' [NoZeroDivisors M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    IsMulTorsionFree M := by
  classical
  refine ⟨fun n hn x y hxy ↦ ?_⟩
  rcases Classical.em (x ≠ 0 ∧ y ≠ 0) with h | h
  · exact ih x h.1 y h.2 n hn hxy
  have : IsReduced M := inferInstance
  grind [eq_zero_of_pow_eq_zero, zero_pow]

variable [UniqueFactorizationMonoid M] [NormalizationMonoid M] [IsMulTorsionFree Mˣ]

namespace UniqueFactorizationMonoid

instance : IsMulTorsionFree M := by
  refine .mk' fun x hx y hy n hn hxy ↦ ?_
  obtain ⟨u, hu⟩ : Associated x y := by
    have := (Associated.of_eq hxy).normalizedFactors_eq
    rwa [normalizedFactors_pow, normalizedFactors_pow, nsmul_right_inj hn,
      ← associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
  replace hx : IsLeftRegular (x ^ n) := (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx).pow n
  rw [← hu, mul_pow, eq_comm, IsLeftRegular.mul_left_eq_self_iff hx, ← Units.val_pow_eq_pow_val,
    Units.val_eq_one, pow_eq_one_iff_left hn] at hxy
  rwa [hxy, Units.val_one, mul_one] at hu

end UniqueFactorizationMonoid

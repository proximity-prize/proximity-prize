/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Kenny Lau,Xavier Roblot
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
section ProximityFlatProofPort
variable {M:Type*} [CommMonoidWithZero M]
theorem IsMulTorsionFree.mk' [NoZeroDivisors M]
    (ih:∀ x≠0,∀ y≠0,∀ n≠0,(x^n:M)=y^n → x=y):
    IsMulTorsionFree M:=by
  classical
  refine ⟨fun n hn x y hxy↦?_⟩
  rcases Classical.em (x≠0∧y≠0) with h | h
  · exact ih x h.1 y h.2 n hn hxy
  have:IsReduced M:=inferInstance
  grind [eq_zero_of_pow_eq_zero,zero_pow]
variable [UniqueFactorizationMonoid M] [NormalizationMonoid M] [IsMulTorsionFree Mˣ]
namespace UniqueFactorizationMonoid
instance:IsMulTorsionFree M:=by
  refine .mk' fun x hx y hy n hn hxy↦?_
  obtain ⟨u,hu⟩:Associated x y:=by
    have:=(Associated.of_eq hxy).normalizedFactors_eq
    rwa [normalizedFactors_pow,normalizedFactors_pow,nsmul_right_inj hn,
      ←associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
  replace hx:IsLeftRegular (x^n):=(IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx).pow n
  rw [←hu,mul_pow,eq_comm,IsLeftRegular.mul_left_eq_self_iff hx, ←Units.val_pow_eq_pow_val,
    Units.val_eq_one,pow_eq_one_iff_left hn] at hxy
  rwa [hxy,Units.val_one,mul_one] at hu
end UniqueFactorizationMonoid
